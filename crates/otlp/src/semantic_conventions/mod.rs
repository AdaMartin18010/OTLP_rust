//! # OpenTelemetry Semantic Conventions
//!
//! This module provides type-safe implementations of OpenTelemetry Semantic Conventions,
//! ensuring consistent attribute naming and values across all telemetry signals.
//!
//! ## Features
//!
//! - **HTTP Conventions**: Client and server HTTP attributes (✅ Stable since 2023)
//! - **Database Conventions**: Database operation attributes (✅ Stable since 2024)
//! - **Messaging Conventions**: Message queue attributes (🔄 In Development)
//! - **K8s Conventions**: Kubernetes resource attributes (✅ Stable)
//! - **RPC Conventions**: gRPC and other RPC framework attributes (✅ Stable)
//! - **GenAI Conventions**: Generative AI operation attributes (🔄 Experimental)
//! - **FaaS Conventions**: Function-as-a-Service attributes (✅ Stable)
//! - **Exception Conventions**: Exception and error handling attributes (✅ Stable)
//! - **Cloud Conventions**: Cloud provider attributes (AWS, Azure, GCP, etc.) (✅ Stable)
//! - **Container Conventions**: Container and Docker attributes (✅ Stable)
//! - **Process Conventions**: Process and runtime attributes (✅ Stable)
//! - **Host Conventions**: Host and device attributes (✅ Stable)
//! - **Resource Conventions**: Service and deployment attributes (✅ Stable)
//!
//! ## 2025-2026 Latest Updates
//!
//! - **Database Conventions**: Marked stable in 2024 (v1.23.0+)
//! - **HTTP Conventions**: Marked stable in 2023 (v1.23.0)
//! - **GenAI Conventions**: New conventions for OpenAI, Anthropic, Azure OpenAI, etc.
//! - **Messaging Conventions**: Advanced stages, expected stabilization soon
//! - **eBPF Support**: OBI (OpenTelemetry eBPF Instrumentation) in Alpha
//! - **Declarative Configuration**: File-based configuration support (YAML/JSON)
//!
//! ## Rust 2024 Features
//!
//! - **Async Closures**: Stabilized in Rust 1.85.0
//! - **Type Safety**: Enum-based values prevent invalid attribute values
//! - **Builder Pattern**: Ergonomic attribute construction
//! - **Constants**: Pre-defined attribute keys for compile-time safety
//! - **Documentation**: Comprehensive examples and usage guidance
//!
//! ## Quick Start
//!
//! ```rust,ignore
//! use otlp::semantic_conventions::http::{HttpAttributesBuilder, HttpMethod};
//!
//! let attrs = HttpAttributesBuilder::new()
//!     .method(HttpMethod::Get)
//!     .status_code(200)
//!     .url("https://api.example.com/users")
//!     .build()?;
//! ```
//!
//! ## Standards
//!
//! Based on OpenTelemetry Semantic Conventions v1.38.0 (2025):
//! - <https://opentelemetry.io/docs/specs/semconv/>
//!
//! OTLP Protocol v1.10.0 (Latest Stable):
//! - <https://opentelemetry.io/docs/specs/otlp/>
//!
//! ## References
//!
//! - [OpenTelemetry Specification Status](https://opentelemetry.io/docs/specs/status/)
//! - [Semantic Conventions Stability Guide](https://opentelemetry.io/docs/specs/semconv/stability/)
//! - [2025 Roadmap](https://opentelemetry.io/blog/2025/go-goals/)

pub mod cloud;
pub mod common;
pub mod container;
pub mod database;
pub mod exception;
pub mod faas;
pub mod gen_ai;
pub mod host;
pub mod http;
pub mod k8s;
pub mod messaging;
pub mod process;
pub mod rpc;
pub mod wasm;

// Re-export commonly used types
pub use cloud::{CloudAttributes, CloudAttributesBuilder, CloudPlatform, CloudProvider};
pub use common::{AttributeKey, AttributeValue, SemanticConventionError};
pub use container::{
    ContainerAttributes, ContainerAttributesBuilder, ContainerRuntime, ContainerState,
};
pub use database::{
    DatabaseAttributes, DatabaseAttributesBuilder, DatabaseOperation, DatabaseSystem,
};
pub use exception::{ErrorType, ExceptionAttributes, ExceptionAttributesBuilder, StackFrame};
pub use faas::{
    FaasAttributes, FaasAttributesBuilder, FaasDocumentOperation, FaasInvocationResult,
    FaasPlatform, FaasTriggerType,
};
pub use gen_ai::{
    GENAI_SEMCONV_STATUS, GENAI_SEMCONV_VERSION, GenAiAttributes, GenAiAttributesBuilder,
    GenAiFinishReason, GenAiOperation, GenAiSystem,
};
pub use host::{DeviceType, HostArch, HostAttributes, HostAttributesBuilder, HostType, OsType};
pub use http::{HttpAttributes, HttpAttributesBuilder, HttpMethod, HttpScheme};
pub use k8s::{K8sAttributes, K8sAttributesBuilder, K8sResourceType};
pub use messaging::{
    DestinationKind, MessagingAttributes, MessagingAttributesBuilder, MessagingOperation,
    MessagingSystem,
};
pub use process::{ProcessAttributes, ProcessAttributesBuilder, ProcessRuntime, ProcessState};
pub use rpc::{RpcAttributes, RpcAttributesBuilder, RpcMessageType, RpcSystem};
pub use wasm::{
    ComponentAttributes, ComponentAttributesBuilder, WasiVersion, WasmAttributes,
    WasmAttributesBuilder, WasmPlatform, WasmRuntime,
};

/// Version of the OpenTelemetry Semantic Conventions implemented
/// Updated to v1.38.0 (2025-2026)
///
/// ## Stability Status
/// - ✅ HTTP: Stable (since 2023)
/// - ✅ Database: Stable (since 2024)
/// - 🔄 Messaging: In Development
/// - ✅ RPC: Stable
/// - 🔄 GenAI: Experimental
/// - ✅ FaaS: Stable
///
/// ## References
/// - <https://opentelemetry.io/docs/specs/semconv/>
pub const SEMCONV_VERSION: &str = "1.38.0";

/// OTLP Protocol version
/// Latest stable: 1.10.0
///
/// ## Key Features in 1.10.0
/// - Full Success / Partial Success / Failure handling
/// - Exponential Histogram support
/// - Profiles signal (Development)
/// - gRPC and HTTP transport
/// - gzip and zstd compression
///
/// ## References  
/// - <https://opentelemetry.io/docs/specs/otlp/>
pub const OTLP_PROTOCOL_VERSION: &str = "1.10.0";

/// Semantic convention status levels
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ConventionStatus {
    /// Stable convention, safe for production use
    Stable,

    /// Experimental convention, may change
    Experimental,

    /// Deprecated convention, avoid use
    Deprecated,
}

/// Get the semantic convention status for a given convention
pub fn get_convention_status(convention: &str) -> Option<ConventionStatus> {
    match convention {
        // Stable conventions
        "http" | "database" | "messaging" | "rpc" | "exception" | "process" | "host"
        | "container" | "cloud" | "faas" => Some(ConventionStatus::Stable),

        // Experimental conventions
        "gen_ai" => Some(ConventionStatus::Experimental),

        // Unknown
        _ => None,
    }
}

/// Check if a semantic convention is stable
pub fn is_stable_convention(convention: &str) -> bool {
    matches!(
        get_convention_status(convention),
        Some(ConventionStatus::Stable)
    )
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_semconv_version() {
        assert_eq!(SEMCONV_VERSION, "1.38.0");
        assert_eq!(OTLP_PROTOCOL_VERSION, "1.10.0");
    }

    #[test]
    fn test_convention_status() {
        assert_eq!(
            get_convention_status("http"),
            Some(ConventionStatus::Stable)
        );
        assert_eq!(
            get_convention_status("database"),
            Some(ConventionStatus::Stable)
        );
        assert_eq!(
            get_convention_status("faas"),
            Some(ConventionStatus::Stable)
        );
        assert_eq!(
            get_convention_status("gen_ai"),
            Some(ConventionStatus::Experimental)
        );
        assert_eq!(get_convention_status("unknown"), None);
    }

    #[test]
    fn test_is_stable_convention() {
        assert!(is_stable_convention("http"));
        assert!(is_stable_convention("exception"));
        assert!(is_stable_convention("cloud"));
        assert!(is_stable_convention("container"));
        assert!(is_stable_convention("process"));
        assert!(is_stable_convention("host"));
        assert!(!is_stable_convention("gen_ai"));
        assert!(!is_stable_convention("unknown"));
    }
}
