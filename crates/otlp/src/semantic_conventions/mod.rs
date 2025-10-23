//! # OpenTelemetry Semantic Conventions
//!
//! This module provides type-safe implementations of OpenTelemetry Semantic Conventions,
//! ensuring consistent attribute naming and values across all telemetry signals.
//!
//! ## Features
//!
//! - **HTTP Conventions**: Client and server HTTP attributes
//! - **Database Conventions**: Database operation attributes
//! - **Messaging Conventions**: Message queue attributes
//! - **K8s Conventions**: Kubernetes resource attributes
//! - **Resource Conventions**: Service and deployment attributes
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
//! Based on OpenTelemetry Semantic Conventions v1.29.0:
//! - https://opentelemetry.io/docs/specs/semconv/

pub mod http;
pub mod common;
pub mod database;
pub mod messaging;
pub mod k8s;

// Re-export commonly used types
pub use http::{HttpAttributes, HttpAttributesBuilder, HttpMethod, HttpScheme};
pub use common::{AttributeKey, AttributeValue, SemanticConventionError};
pub use database::{DatabaseAttributes, DatabaseAttributesBuilder, DatabaseSystem, DatabaseOperation};
pub use messaging::{MessagingAttributes, MessagingAttributesBuilder, MessagingSystem, MessagingOperation, DestinationKind};
pub use k8s::{K8sAttributes, K8sAttributesBuilder, K8sResourceType};

/// Version of the OpenTelemetry Semantic Conventions implemented
pub const SEMCONV_VERSION: &str = "1.29.0";

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

