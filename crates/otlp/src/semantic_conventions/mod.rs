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
//! ## Rust 1.92 特性应用
//!
//! - **常量泛型**: 使用常量泛型优化属性键值对大小
//! - **改进的类型系统**: 利用 Rust 1.92 的类型系统优化提升性能
//! - **元组收集**: 使用 `collect()` 直接收集属性到元组
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

pub mod common;
pub mod database;
pub mod http;
pub mod k8s;
pub mod messaging;

// Re-export commonly used types
pub use common::{AttributeKey, AttributeValue, SemanticConventionError};
pub use database::{
    DatabaseAttributes, DatabaseAttributesBuilder, DatabaseOperation, DatabaseSystem,
};
pub use http::{HttpAttributes, HttpAttributesBuilder, HttpMethod, HttpScheme};
pub use k8s::{K8sAttributes, K8sAttributesBuilder, K8sResourceType};
pub use messaging::{
    DestinationKind, MessagingAttributes, MessagingAttributesBuilder, MessagingOperation,
    MessagingSystem,
};

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
