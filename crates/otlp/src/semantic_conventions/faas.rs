//! # Function-as-a-Service (FaaS) Semantic Conventions
//!
//! Implementation of OpenTelemetry FaaS Semantic Conventions v1.38.0
//! <https://opentelemetry.io/docs/specs/semconv/faas/faas-spans/>
//!
//! ## Supported Platforms
//!
//! - **AWS Lambda**: AWS serverless functions
//! - **Azure Functions**: Microsoft Azure serverless compute
//! - **Google Cloud Functions**: GCP serverless functions
//! - **Alibaba Cloud Function Compute**: Alibaba serverless
//! - **Tencent Cloud SCF**: Tencent serverless cloud functions
//!
//! ## Rust 1.92 Features
//!
//! - **Type-safe triggers**: Enum-based trigger type definitions
//! - **Builder pattern**: Ergonomic attribute construction
//! - **Platform abstractions**: Generic FaaS attributes across providers
//!
//! ## Usage Example
//!
//! ```rust
//! use otlp::semantic_conventions::faas::{
//!     FaasAttributesBuilder, FaasTriggerType, FaasPlatform,
//! };
//!
//! let attrs = FaasAttributesBuilder::new()
//!     .platform(FaasPlatform::AwsLambda)
//!     .function_name("user-processor")
//!     .function_version("1.2.3")
//!     .trigger(FaasTriggerType::Http)
//!     .cold_start(true)
//!     .request_id("abc-123-def")
//!     .build()
//!     .unwrap();
//! ```

use super::common::{AttributeMap, AttributeValue, Result, SemanticConventionError};
use std::collections::HashMap;

/// FaaS platforms/providers
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum FaasPlatform {
    /// AWS Lambda
    AwsLambda,
    /// Azure Functions
    AzureFunctions,
    /// Google Cloud Functions
    GcpCloudFunctions,
    /// Google Cloud Run
    GcpCloudRun,
    /// Alibaba Cloud Function Compute
    AlibabaCloudFc,
    /// Tencent Cloud Serverless Cloud Function
    TencentCloudScf,
    /// OpenFaaS
    OpenFaas,
    /// Knative
    Knative,
    /// Other platform
    Other,
}

impl FaasPlatform {
    /// Returns the string representation of the platform
    pub fn as_str(&self) -> &'static str {
        match self {
            FaasPlatform::AwsLambda => "aws_lambda",
            FaasPlatform::AzureFunctions => "azure_functions",
            FaasPlatform::GcpCloudFunctions => "gcp_cloud_functions",
            FaasPlatform::GcpCloudRun => "gcp_cloud_run",
            FaasPlatform::AlibabaCloudFc => "alibaba_cloud_fc",
            FaasPlatform::TencentCloudScf => "tencent_cloud_scf",
            FaasPlatform::OpenFaas => "openfaas",
            FaasPlatform::Knative => "knative",
            FaasPlatform::Other => "other",
        }
    }
}

impl std::fmt::Display for FaasPlatform {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.as_str())
    }
}

/// FaaS trigger types
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum FaasTriggerType {
    /// HTTP request trigger
    Http,
    /// Timer/scheduled trigger
    Timer,
    /// Message queue trigger (SQS, Event Hub, Pub/Sub)
    Queue,
    /// Event trigger (S3, EventBridge, Event Grid)
    Event,
    /// Pub/Sub trigger
    Pubsub,
    /// Database trigger
    Database,
    /// Datastream trigger
    Datastream,
    /// Other trigger type
    Other,
}

impl FaasTriggerType {
    /// Returns the string representation of the trigger type
    pub fn as_str(&self) -> &'static str {
        match self {
            FaasTriggerType::Http => "http",
            FaasTriggerType::Timer => "timer",
            FaasTriggerType::Queue => "queue",
            FaasTriggerType::Event => "event",
            FaasTriggerType::Pubsub => "pubsub",
            FaasTriggerType::Database => "database",
            FaasTriggerType::Datastream => "datastream",
            FaasTriggerType::Other => "other",
        }
    }
}

impl std::fmt::Display for FaasTriggerType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.as_str())
    }
}

/// FaaS document operation types
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum FaasDocumentOperation {
    /// Document created
    Insert,
    /// Document modified
    Edit,
    /// Document deleted
    Delete,
}

impl FaasDocumentOperation {
    /// Returns the string representation
    pub fn as_str(&self) -> &'static str {
        match self {
            FaasDocumentOperation::Insert => "insert",
            FaasDocumentOperation::Edit => "edit",
            FaasDocumentOperation::Delete => "delete",
        }
    }
}

/// FaaS invocation result
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum FaasInvocationResult {
    /// Successful invocation
    Success,
    /// Failed invocation
    Failure,
}

impl FaasInvocationResult {
    /// Returns the string representation
    pub fn as_str(&self) -> &'static str {
        match self {
            FaasInvocationResult::Success => "success",
            FaasInvocationResult::Failure => "failure",
        }
    }
}

/// FaaS attributes following OpenTelemetry semantic conventions
#[derive(Debug, Clone)]
pub struct FaasAttributes {
    attributes: AttributeMap,
}

impl FaasAttributes {
    /// Get all attributes as a map
    pub fn as_map(&self) -> &AttributeMap {
        &self.attributes
    }

    /// Get a specific attribute
    pub fn get(&self, key: &str) -> Option<&AttributeValue> {
        self.attributes.get(key)
    }
}

/// Builder for FaaS attributes
#[derive(Debug, Default)]
pub struct FaasAttributesBuilder {
    // Required attributes
    platform: Option<FaasPlatform>,
    function_name: Option<String>,

    // Function configuration
    function_version: Option<String>,
    max_memory: Option<i64>,
    timeout: Option<i64>,

    // Execution context
    cold_start: Option<bool>,
    request_id: Option<String>,
    invocation_id: Option<String>,

    // Trigger information
    trigger_type: Option<FaasTriggerType>,
    trigger_source: Option<String>,

    // Document triggers
    document_collection: Option<String>,
    document_operation: Option<FaasDocumentOperation>,
    document_time: Option<String>,
    document_name: Option<String>,

    // Message triggers
    message_id: Option<String>,

    // Invoked by
    invoked_provider: Option<FaasPlatform>,
    invoked_region: Option<String>,
    invoked_name: Option<String>,

    // Result
    invocation_result: Option<FaasInvocationResult>,

    // Custom attributes
    custom: HashMap<String, AttributeValue>,
}

impl FaasAttributesBuilder {
    /// Create a new builder
    pub fn new() -> Self {
        Self::default()
    }

    /// Set FaaS platform/provider (required)
    pub fn platform(mut self, platform: FaasPlatform) -> Self {
        self.platform = Some(platform);
        self
    }

    /// Set function name (required)
    pub fn function_name(mut self, name: impl Into<String>) -> Self {
        self.function_name = Some(name.into());
        self
    }

    /// Set function version
    pub fn function_version(mut self, version: impl Into<String>) -> Self {
        self.function_version = Some(version.into());
        self
    }

    /// Set maximum memory in MB
    pub fn max_memory(mut self, memory_mb: i64) -> Self {
        self.max_memory = Some(memory_mb);
        self
    }

    /// Set function timeout in milliseconds
    pub fn timeout(mut self, timeout_ms: i64) -> Self {
        self.timeout = Some(timeout_ms);
        self
    }

    /// Set cold start indicator
    pub fn cold_start(mut self, is_cold_start: bool) -> Self {
        self.cold_start = Some(is_cold_start);
        self
    }

    /// Set request ID
    pub fn request_id(mut self, id: impl Into<String>) -> Self {
        self.request_id = Some(id.into());
        self
    }

    /// Set invocation ID
    pub fn invocation_id(mut self, id: impl Into<String>) -> Self {
        self.invocation_id = Some(id.into());
        self
    }

    /// Set trigger type
    pub fn trigger(mut self, trigger: FaasTriggerType) -> Self {
        self.trigger_type = Some(trigger);
        self
    }

    /// Set trigger source/ARN
    pub fn trigger_source(mut self, source: impl Into<String>) -> Self {
        self.trigger_source = Some(source.into());
        self
    }

    /// Set document collection (for document triggers)
    pub fn document_collection(mut self, collection: impl Into<String>) -> Self {
        self.document_collection = Some(collection.into());
        self
    }

    /// Set document operation
    pub fn document_operation(mut self, operation: FaasDocumentOperation) -> Self {
        self.document_operation = Some(operation);
        self
    }

    /// Set document time
    pub fn document_time(mut self, time: impl Into<String>) -> Self {
        self.document_time = Some(time.into());
        self
    }

    /// Set document name
    pub fn document_name(mut self, name: impl Into<String>) -> Self {
        self.document_name = Some(name.into());
        self
    }

    /// Set message ID
    pub fn message_id(mut self, id: impl Into<String>) -> Self {
        self.message_id = Some(id.into());
        self
    }

    /// Set invoked provider (for chained invocations)
    pub fn invoked_provider(mut self, provider: FaasPlatform) -> Self {
        self.invoked_provider = Some(provider);
        self
    }

    /// Set invoked region
    pub fn invoked_region(mut self, region: impl Into<String>) -> Self {
        self.invoked_region = Some(region.into());
        self
    }

    /// Set invoked function name
    pub fn invoked_name(mut self, name: impl Into<String>) -> Self {
        self.invoked_name = Some(name.into());
        self
    }

    /// Set invocation result
    pub fn invocation_result(mut self, result: FaasInvocationResult) -> Self {
        self.invocation_result = Some(result);
        self
    }

    /// Add a custom attribute
    pub fn custom_attribute(mut self, key: impl Into<String>, value: AttributeValue) -> Self {
        self.custom.insert(key.into(), value);
        self
    }

    /// Build the FaaS attributes
    pub fn build(self) -> Result<FaasAttributes> {
        let platform = self
            .platform
            .ok_or_else(|| SemanticConventionError::MissingRequired("faas.platform".to_string()))?;

        let function_name = self
            .function_name
            .ok_or_else(|| SemanticConventionError::MissingRequired("faas.name".to_string()))?;

        let mut attributes = AttributeMap::new();

        // Required attributes
        attributes.insert(
            "faas.name".to_string(),
            AttributeValue::String(function_name),
        );
        attributes.insert(
            "cloud.platform".to_string(),
            AttributeValue::String(platform.as_str().to_string()),
        );

        // Optional attributes
        if let Some(version) = self.function_version {
            attributes.insert("faas.version".to_string(), AttributeValue::String(version));
        }

        if let Some(memory) = self.max_memory {
            attributes.insert("faas.max_memory".to_string(), AttributeValue::Int(memory));
        }

        if let Some(timeout) = self.timeout {
            attributes.insert("faas.timeout".to_string(), AttributeValue::Int(timeout));
        }

        if let Some(cold_start) = self.cold_start {
            attributes.insert(
                "faas.coldstart".to_string(),
                AttributeValue::Bool(cold_start),
            );
        }

        if let Some(request_id) = self.request_id {
            attributes.insert(
                "faas.invocation_id".to_string(),
                AttributeValue::String(request_id),
            );
        }

        if let Some(invocation_id) = self.invocation_id {
            attributes.insert(
                "faas.invocation_id".to_string(),
                AttributeValue::String(invocation_id),
            );
        }

        if let Some(trigger) = self.trigger_type {
            attributes.insert(
                "faas.trigger".to_string(),
                AttributeValue::String(trigger.as_str().to_string()),
            );
        }

        if let Some(source) = self.trigger_source {
            attributes.insert(
                "faas.trigger_source".to_string(),
                AttributeValue::String(source),
            );
        }

        if let Some(collection) = self.document_collection {
            attributes.insert(
                "faas.document.collection".to_string(),
                AttributeValue::String(collection),
            );
        }

        if let Some(operation) = self.document_operation {
            attributes.insert(
                "faas.document.operation".to_string(),
                AttributeValue::String(operation.as_str().to_string()),
            );
        }

        if let Some(time) = self.document_time {
            attributes.insert(
                "faas.document.time".to_string(),
                AttributeValue::String(time),
            );
        }

        if let Some(name) = self.document_name {
            attributes.insert(
                "faas.document.name".to_string(),
                AttributeValue::String(name),
            );
        }

        if let Some(msg_id) = self.message_id {
            attributes.insert(
                "messaging.message.id".to_string(),
                AttributeValue::String(msg_id),
            );
        }

        if let Some(provider) = self.invoked_provider {
            attributes.insert(
                "faas.invoked_provider".to_string(),
                AttributeValue::String(provider.as_str().to_string()),
            );
        }

        if let Some(region) = self.invoked_region {
            attributes.insert(
                "faas.invoked_region".to_string(),
                AttributeValue::String(region),
            );
        }

        if let Some(name) = self.invoked_name {
            attributes.insert(
                "faas.invoked_name".to_string(),
                AttributeValue::String(name),
            );
        }

        if let Some(result) = self.invocation_result {
            attributes.insert(
                "faas.invocation_result".to_string(),
                AttributeValue::String(result.as_str().to_string()),
            );
        }

        // Add custom attributes
        attributes.extend(self.custom);

        Ok(FaasAttributes { attributes })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_faas_platform() {
        assert_eq!(FaasPlatform::AwsLambda.as_str(), "aws_lambda");
        assert_eq!(FaasPlatform::AzureFunctions.as_str(), "azure_functions");
        assert_eq!(
            FaasPlatform::GcpCloudFunctions.as_str(),
            "gcp_cloud_functions"
        );
    }

    #[test]
    fn test_faas_trigger_type() {
        assert_eq!(FaasTriggerType::Http.as_str(), "http");
        assert_eq!(FaasTriggerType::Timer.as_str(), "timer");
        assert_eq!(FaasTriggerType::Queue.as_str(), "queue");
        assert_eq!(FaasTriggerType::Event.as_str(), "event");
    }

    #[test]
    fn test_faas_attributes_builder_minimal() {
        let attrs = FaasAttributesBuilder::new()
            .platform(FaasPlatform::AwsLambda)
            .function_name("test-function")
            .build()
            .unwrap();

        assert_eq!(
            attrs.get("faas.name"),
            Some(&AttributeValue::String("test-function".to_string()))
        );
        assert_eq!(
            attrs.get("cloud.platform"),
            Some(&AttributeValue::String("aws_lambda".to_string()))
        );
    }

    #[test]
    fn test_faas_attributes_builder_full() {
        let attrs = FaasAttributesBuilder::new()
            .platform(FaasPlatform::AwsLambda)
            .function_name("user-processor")
            .function_version("1.2.3")
            .max_memory(512)
            .timeout(30000)
            .cold_start(true)
            .request_id("abc-123-def")
            .trigger(FaasTriggerType::Http)
            .trigger_source("API Gateway")
            .invocation_result(FaasInvocationResult::Success)
            .build()
            .unwrap();

        assert_eq!(
            attrs.get("faas.version"),
            Some(&AttributeValue::String("1.2.3".to_string()))
        );
        assert_eq!(
            attrs.get("faas.max_memory"),
            Some(&AttributeValue::Int(512))
        );
        assert_eq!(
            attrs.get("faas.coldstart"),
            Some(&AttributeValue::Bool(true))
        );
        assert_eq!(
            attrs.get("faas.trigger"),
            Some(&AttributeValue::String("http".to_string()))
        );
    }

    #[test]
    fn test_faas_document_trigger() {
        let attrs = FaasAttributesBuilder::new()
            .platform(FaasPlatform::AzureFunctions)
            .function_name("document-processor")
            .trigger(FaasTriggerType::Database)
            .document_collection("users")
            .document_operation(FaasDocumentOperation::Insert)
            .document_name("user123")
            .build()
            .unwrap();

        assert_eq!(
            attrs.get("faas.document.collection"),
            Some(&AttributeValue::String("users".to_string()))
        );
        assert_eq!(
            attrs.get("faas.document.operation"),
            Some(&AttributeValue::String("insert".to_string()))
        );
    }

    #[test]
    fn test_faas_invoked_chain() {
        let attrs = FaasAttributesBuilder::new()
            .platform(FaasPlatform::GcpCloudFunctions)
            .function_name("downstream-function")
            .invoked_provider(FaasPlatform::AwsLambda)
            .invoked_region("us-east-1")
            .invoked_name("upstream-function")
            .build()
            .unwrap();

        assert_eq!(
            attrs.get("faas.invoked_provider"),
            Some(&AttributeValue::String("aws_lambda".to_string()))
        );
        assert_eq!(
            attrs.get("faas.invoked_region"),
            Some(&AttributeValue::String("us-east-1".to_string()))
        );
    }

    #[test]
    fn test_faas_attributes_builder_missing_required() {
        let result = FaasAttributesBuilder::new().function_name("test").build();

        assert!(result.is_err());
        match result {
            Err(SemanticConventionError::MissingRequired(field)) => {
                assert_eq!(field, "faas.platform");
            }
            _ => panic!("Expected MissingRequired error for platform"),
        }

        let result = FaasAttributesBuilder::new()
            .platform(FaasPlatform::AwsLambda)
            .build();

        assert!(result.is_err());
        match result {
            Err(SemanticConventionError::MissingRequired(field)) => {
                assert_eq!(field, "faas.name");
            }
            _ => panic!("Expected MissingRequired error for name"),
        }
    }

    #[test]
    fn test_faas_custom_attributes() {
        let attrs = FaasAttributesBuilder::new()
            .platform(FaasPlatform::Knative)
            .function_name("custom-fn")
            .custom_attribute("custom.key1", AttributeValue::String("value1".to_string()))
            .custom_attribute("custom.key2", AttributeValue::Int(42))
            .build()
            .unwrap();

        assert_eq!(
            attrs.get("custom.key1"),
            Some(&AttributeValue::String("value1".to_string()))
        );
        assert_eq!(attrs.get("custom.key2"), Some(&AttributeValue::Int(42)));
    }
}
