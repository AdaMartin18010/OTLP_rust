//! # RPC Semantic Conventions
//!
//! Implementation of OpenTelemetry RPC Semantic Conventions v1.38.0
//! <https://opentelemetry.io/docs/specs/semconv/rpc/>
//!
//! ## Features
//!
//! - **gRPC Support**: Full gRPC attribute coverage
//! - **General RPC**: Framework-agnostic RPC attributes
//! - **Type-Safe Builders**: Builder pattern for constructing attributes

use super::common::{AttributeMap, AttributeValue};

/// RPC system identifiers
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum RpcSystem {
    /// gRPC
    Grpc,
    /// Java RMI
    JavaRmi,
    /// .NET WCF
    DotNetWcf,
    /// Apache Dubbo
    ApacheDubbo,
    /// Twitter Finagle
    Finagle,
    /// Custom RPC system
    Custom(&'static str),
}

impl RpcSystem {
    pub fn as_str(&self) -> &str {
        match self {
            RpcSystem::Grpc => "grpc",
            RpcSystem::JavaRmi => "java_rmi",
            RpcSystem::DotNetWcf => "dotnet_wcf",
            RpcSystem::ApacheDubbo => "apache_dubbo",
            RpcSystem::Finagle => "finagle",
            RpcSystem::Custom(s) => s,
        }
    }
}

impl std::fmt::Display for RpcSystem {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.as_str())
    }
}

/// RPC message types
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum RpcMessageType {
    /// Client request
    Sent,
    /// Server response
    Received,
}

impl RpcMessageType {
    pub fn as_str(&self) -> &str {
        match self {
            RpcMessageType::Sent => "SENT",
            RpcMessageType::Received => "RECEIVED",
        }
    }
}

/// RPC attributes following OpenTelemetry conventions
#[derive(Debug, Clone)]
pub struct RpcAttributes {
    attributes: AttributeMap,
}

impl RpcAttributes {
    /// Get all attributes as a map
    pub fn as_map(&self) -> &AttributeMap {
        &self.attributes
    }

    /// Get a specific attribute
    pub fn get(&self, key: &str) -> Option<&AttributeValue> {
        self.attributes.get(key)
    }

    /// Create a new builder
    pub fn builder() -> RpcAttributesBuilder {
        RpcAttributesBuilder::default()
    }
}

/// Builder for RPC attributes
#[derive(Debug, Default)]
pub struct RpcAttributesBuilder {
    system: Option<RpcSystem>,
    service: Option<String>,
    method: Option<String>,
    status_code: Option<i64>,
    message_type: Option<RpcMessageType>,
    message_id: Option<i64>,
    message_compressed_size: Option<i64>,
    message_uncompressed_size: Option<i64>,
}

impl RpcAttributesBuilder {
    /// Set the RPC system
    pub fn system(mut self, system: RpcSystem) -> Self {
        self.system = Some(system);
        self
    }

    /// Set the service name (full qualified service name)
    pub fn service(mut self, service: impl Into<String>) -> Self {
        self.service = Some(service.into());
        self
    }

    /// Set the method name
    pub fn method(mut self, method: impl Into<String>) -> Self {
        self.method = Some(method.into());
        self
    }

    /// Set the status code
    pub fn status_code(mut self, code: i64) -> Self {
        self.status_code = Some(code);
        self
    }

    /// Set the message type
    pub fn message_type(mut self, msg_type: RpcMessageType) -> Self {
        self.message_type = Some(msg_type);
        self
    }

    /// Set the message ID
    pub fn message_id(mut self, id: i64) -> Self {
        self.message_id = Some(id);
        self
    }

    /// Set the compressed message size
    pub fn message_compressed_size(mut self, size: i64) -> Self {
        self.message_compressed_size = Some(size);
        self
    }

    /// Set the uncompressed message size
    pub fn message_uncompressed_size(mut self, size: i64) -> Self {
        self.message_uncompressed_size = Some(size);
        self
    }

    /// Build the RPC attributes
    pub fn build(self) -> RpcAttributes {
        let mut attributes = AttributeMap::new();

        if let Some(system) = self.system {
            attributes.insert(
                "rpc.system".to_string(),
                AttributeValue::String(system.as_str().to_string()),
            );
        }

        if let Some(service) = self.service {
            attributes.insert("rpc.service".to_string(), AttributeValue::String(service));
        }

        if let Some(method) = self.method {
            attributes.insert("rpc.method".to_string(), AttributeValue::String(method));
        }

        if let Some(status_code) = self.status_code {
            attributes.insert(
                "rpc.grpc.status_code".to_string(),
                AttributeValue::Int(status_code),
            );
        }

        if let Some(msg_type) = self.message_type {
            attributes.insert(
                "rpc.message.type".to_string(),
                AttributeValue::String(msg_type.as_str().to_string()),
            );
        }

        if let Some(msg_id) = self.message_id {
            attributes.insert("rpc.message.id".to_string(), AttributeValue::Int(msg_id));
        }

        if let Some(size) = self.message_compressed_size {
            attributes.insert(
                "rpc.message.compressed_size".to_string(),
                AttributeValue::Int(size),
            );
        }

        if let Some(size) = self.message_uncompressed_size {
            attributes.insert(
                "rpc.message.uncompressed_size".to_string(),
                AttributeValue::Int(size),
            );
        }

        RpcAttributes { attributes }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_rpc_system_as_str() {
        assert_eq!(RpcSystem::Grpc.as_str(), "grpc");
        assert_eq!(RpcSystem::JavaRmi.as_str(), "java_rmi");
        assert_eq!(RpcSystem::Custom("custom_rpc").as_str(), "custom_rpc");
    }

    #[test]
    fn test_rpc_attributes_builder() {
        let attrs = RpcAttributes::builder()
            .system(RpcSystem::Grpc)
            .service("my.package.Service")
            .method("GetUser")
            .status_code(0)
            .build();

        assert_eq!(
            attrs.get("rpc.system"),
            Some(&AttributeValue::String("grpc".to_string()))
        );
        assert_eq!(
            attrs.get("rpc.service"),
            Some(&AttributeValue::String("my.package.Service".to_string()))
        );
        assert_eq!(
            attrs.get("rpc.method"),
            Some(&AttributeValue::String("GetUser".to_string()))
        );
        assert_eq!(
            attrs.get("rpc.grpc.status_code"),
            Some(&AttributeValue::Int(0))
        );
    }

    #[test]
    fn test_message_attributes() {
        let attrs = RpcAttributes::builder()
            .system(RpcSystem::Grpc)
            .message_type(RpcMessageType::Sent)
            .message_id(1)
            .message_compressed_size(100)
            .message_uncompressed_size(200)
            .build();

        assert_eq!(
            attrs.get("rpc.message.type"),
            Some(&AttributeValue::String("SENT".to_string()))
        );
        assert_eq!(attrs.get("rpc.message.id"), Some(&AttributeValue::Int(1)));
        assert_eq!(
            attrs.get("rpc.message.compressed_size"),
            Some(&AttributeValue::Int(100))
        );
        assert_eq!(
            attrs.get("rpc.message.uncompressed_size"),
            Some(&AttributeValue::Int(200))
        );
    }
}
