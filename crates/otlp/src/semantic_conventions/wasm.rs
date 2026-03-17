//! # WebAssembly Semantic Conventions
//!
//! OpenTelemetry semantic conventions for WebAssembly environments.
//! Defines standard attributes for WASM runtimes, modules, and execution contexts.
//!
//! ## 2025-2026 WebAssembly Observability Context
//!
//! WebAssembly is becoming a major target for observability with:
//!
//! - **wasmCloud**: CNCF sandbox project with OpenTelemetry integration
//! - **Spin 3.0**: Built-in OTEL support for serverless WASM
//! - **WASI Preview 2**: Standardized system interfaces with HTTP support
//! - **Component Model**: Cross-language composition with typed interfaces
//!
//! ## Standard Attributes
//!
//! ### WebAssembly Runtime
//!
//! | Attribute | Type | Description | Example |
//! |-----------|------|-------------|---------|
//! | `wasm.runtime.name` | string | WASM runtime name | `wasmtime`, `wasmer`, `wasmcloud` |
//! | `wasm.runtime.version` | string | Runtime version | `15.0.0` |
//! | `wasm.runtime.wasi_version` | string | WASI version | `preview1`, `preview2` |
//!
//! ### WebAssembly Module
//!
//! | Attribute | Type | Description | Example |
//! |-----------|------|-------------|---------|
//! | `wasm.module.name` | string | Module name | `my-component` |
//! | `wasm.module.version` | string | Module version | `1.2.3` |
//! | `wasm.module.hash` | string | Module SHA256 hash | `abc123...` |
//! | `wasm.module.source` | string | Source URL or path | `file:///app.wasm` |
//! | `wasm.module.language` | string | Source language | `rust`, `go`, `typescript` |
//!
//! ### WebAssembly Component (Component Model)
//!
//! | Attribute | Type | Description | Example |
//! |-----------|------|-------------|---------|
//! | `wasm.component.id` | string | Component identifier | `my-component` |
//! | `wasm.component.version` | string | Component version | `1.0.0` |
//! | `wasm.component.package` | string | Package reference | `example:my-component` |
//! | `wasm.component.interface` | string | Implemented interface | `wasi:http/incoming-handler` |
//!
//! ### WebAssembly Instance
//!
//! | Attribute | Type | Description | Example |
//! |-----------|------|-------------|---------|
//! | `wasm.instance.id` | string | Instance identifier | `instance-abc123` |
//! | `wasm.instance.memory_limit` | int | Memory limit in bytes | `134217728` |
//! | `wasm.instance.memory_usage` | int | Current memory usage | `67108864` |
//! | `wasm.instance.execution_count` | int | Total executions | `1000` |
//!
//! ### WebAssembly Platform
//!
//! | Attribute | Type | Description | Example |
//! |-----------|------|-------------|---------|
//! | `wasm.platform.type` | string | Platform type | `browser`, `server`, `edge` |
//! | `wasm.platform.host` | string | Host environment | `spin`, `wasmcloud`, `custom` |
//!
//! ## Usage Examples
//!
//! ### Basic WASM Module Attributes
//!
//! ```rust,ignore
//! use otlp::semantic_conventions::wasm::WasmAttributes;
//!
//! let attrs = WasmAttributes::builder()
//!     .runtime_name("wasmtime")
//!     .runtime_version("15.0.0")
//!     .wasi_version("preview2")
//!     .module_name("my-component")
//!     .module_version("1.0.0")
//!     .build();
//! ```
//!
//! ### Component Model Attributes
//!
//! ```rust,ignore
//! use otlp::semantic_conventions::wasm::ComponentAttributes;
//!
//! let attrs = ComponentAttributes::builder()
//!     .component_id("http-handler")
//!     .package("example:http-handler")
//!     .interface("wasi:http/incoming-handler")
//!     .build();
//! ```
//!
//! ## References
//!
//! - [WASI Specification](https://github.com/WebAssembly/WASI)
//! - [Component Model](https://component-model.bytecodealliance.org/)
//! - [wasmCloud OpenTelemetry](https://wasmcloud.com/docs/deployment/observability/otel)
//! - [Spin Observability](https://developer.fermyon.com/spin/v3/observing-apps)

use super::common::{AttributeMap, AttributeValue, ToAttributeValue};

/// Standard attribute keys for WebAssembly
pub mod keys {
    // Runtime attributes
    pub const WASM_RUNTIME_NAME: &str = "wasm.runtime.name";
    pub const WASM_RUNTIME_VERSION: &str = "wasm.runtime.version";
    pub const WASM_RUNTIME_WASI_VERSION: &str = "wasm.runtime.wasi_version";

    // Module attributes
    pub const WASM_MODULE_NAME: &str = "wasm.module.name";
    pub const WASM_MODULE_VERSION: &str = "wasm.module.version";
    pub const WASM_MODULE_HASH: &str = "wasm.module.hash";
    pub const WASM_MODULE_SOURCE: &str = "wasm.module.source";
    pub const WASM_MODULE_LANGUAGE: &str = "wasm.module.language";

    // Component attributes
    pub const WASM_COMPONENT_ID: &str = "wasm.component.id";
    pub const WASM_COMPONENT_VERSION: &str = "wasm.component.version";
    pub const WASM_COMPONENT_PACKAGE: &str = "wasm.component.package";
    pub const WASM_COMPONENT_INTERFACE: &str = "wasm.component.interface";

    // Instance attributes
    pub const WASM_INSTANCE_ID: &str = "wasm.instance.id";
    pub const WASM_INSTANCE_MEMORY_LIMIT: &str = "wasm.instance.memory_limit";
    pub const WASM_INSTANCE_MEMORY_USAGE: &str = "wasm.instance.memory_usage";
    pub const WASM_INSTANCE_EXECUTION_COUNT: &str = "wasm.instance.execution_count";

    // Platform attributes
    pub const WASM_PLATFORM_TYPE: &str = "wasm.platform.type";
    pub const WASM_PLATFORM_HOST: &str = "wasm.platform.host";
}

/// WASM runtime types
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum WasmRuntime {
    /// Wasmtime runtime
    Wasmtime,
    /// Wasmer runtime
    Wasmer,
    /// WasmEdge runtime
    WasmEdge,
    /// wasmCloud runtime
    WasmCloud,
    /// Spin runtime
    Spin,
    /// Browser WASM
    Browser,
    /// Node.js WASM
    NodeJS,
    /// Other/Unknown
    Other,
}

impl WasmRuntime {
    /// Get the runtime name as a string
    pub fn as_str(&self) -> &'static str {
        match self {
            WasmRuntime::Wasmtime => "wasmtime",
            WasmRuntime::Wasmer => "wasmer",
            WasmRuntime::WasmEdge => "wasmedge",
            WasmRuntime::WasmCloud => "wasmcloud",
            WasmRuntime::Spin => "spin",
            WasmRuntime::Browser => "browser",
            WasmRuntime::NodeJS => "nodejs",
            WasmRuntime::Other => "other",
        }
    }
}

impl std::fmt::Display for WasmRuntime {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.as_str())
    }
}

/// WASI version
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum WasiVersion {
    /// WASI Preview 1
    Preview1,
    /// WASI Preview 2
    Preview2,
    /// WASI Preview 3 (expected)
    Preview3,
    /// No WASI (browser or embedded)
    None,
}

impl WasiVersion {
    /// Get the version string
    pub fn as_str(&self) -> &'static str {
        match self {
            WasiVersion::Preview1 => "preview1",
            WasiVersion::Preview2 => "preview2",
            WasiVersion::Preview3 => "preview3",
            WasiVersion::None => "none",
        }
    }
}

/// WASM platform types
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum WasmPlatform {
    /// Browser environment
    Browser,
    /// Server-side (WASI)
    Server,
    /// Edge computing
    Edge,
    /// IoT/Embedded
    Embedded,
}

impl WasmPlatform {
    /// Get the platform type string
    pub fn as_str(&self) -> &'static str {
        match self {
            WasmPlatform::Browser => "browser",
            WasmPlatform::Server => "server",
            WasmPlatform::Edge => "edge",
            WasmPlatform::Embedded => "embedded",
        }
    }
}

/// WebAssembly attributes builder
#[derive(Debug, Default)]
pub struct WasmAttributesBuilder {
    attributes: AttributeMap,
}

impl WasmAttributesBuilder {
    /// Create a new builder
    pub fn new() -> Self {
        Self {
            attributes: AttributeMap::new(),
        }
    }

    /// Set runtime name
    pub fn runtime_name(mut self, name: impl Into<String>) -> Self {
        self.attributes.insert(
            keys::WASM_RUNTIME_NAME.into(),
            name.into().to_attribute_value(),
        );
        self
    }

    /// Set runtime version
    pub fn runtime_version(mut self, version: impl Into<String>) -> Self {
        self.attributes.insert(
            keys::WASM_RUNTIME_VERSION.into(),
            version.into().to_attribute_value(),
        );
        self
    }

    /// Set WASI version
    pub fn wasi_version(mut self, version: WasiVersion) -> Self {
        self.attributes.insert(
            keys::WASM_RUNTIME_WASI_VERSION.into(),
            version.as_str().to_attribute_value(),
        );
        self
    }

    /// Set module name
    pub fn module_name(mut self, name: impl Into<String>) -> Self {
        self.attributes.insert(
            keys::WASM_MODULE_NAME.into(),
            name.into().to_attribute_value(),
        );
        self
    }

    /// Set module version
    pub fn module_version(mut self, version: impl Into<String>) -> Self {
        self.attributes.insert(
            keys::WASM_MODULE_VERSION.into(),
            version.into().to_attribute_value(),
        );
        self
    }

    /// Set module hash
    pub fn module_hash(mut self, hash: impl Into<String>) -> Self {
        self.attributes.insert(
            keys::WASM_MODULE_HASH.into(),
            hash.into().to_attribute_value(),
        );
        self
    }

    /// Set module source
    pub fn module_source(mut self, source: impl Into<String>) -> Self {
        self.attributes.insert(
            keys::WASM_MODULE_SOURCE.into(),
            source.into().to_attribute_value(),
        );
        self
    }

    /// Set source language
    pub fn module_language(mut self, language: impl Into<String>) -> Self {
        self.attributes.insert(
            keys::WASM_MODULE_LANGUAGE.into(),
            language.into().to_attribute_value(),
        );
        self
    }

    /// Set instance ID
    pub fn instance_id(mut self, id: impl Into<String>) -> Self {
        self.attributes.insert(
            keys::WASM_INSTANCE_ID.into(),
            id.into().to_attribute_value(),
        );
        self
    }

    /// Set memory limit in bytes
    pub fn memory_limit(mut self, limit: i64) -> Self {
        self.attributes.insert(
            keys::WASM_INSTANCE_MEMORY_LIMIT.into(),
            AttributeValue::Int(limit),
        );
        self
    }

    /// Set memory usage in bytes
    pub fn memory_usage(mut self, usage: i64) -> Self {
        self.attributes.insert(
            keys::WASM_INSTANCE_MEMORY_USAGE.into(),
            AttributeValue::Int(usage),
        );
        self
    }

    /// Set platform type
    pub fn platform_type(mut self, platform: WasmPlatform) -> Self {
        self.attributes.insert(
            keys::WASM_PLATFORM_TYPE.into(),
            platform.as_str().to_attribute_value(),
        );
        self
    }

    /// Set platform host
    pub fn platform_host(mut self, host: impl Into<String>) -> Self {
        self.attributes.insert(
            keys::WASM_PLATFORM_HOST.into(),
            host.into().to_attribute_value(),
        );
        self
    }

    /// Build the attributes
    pub fn build(self) -> WasmAttributes {
        WasmAttributes {
            attributes: self.attributes,
        }
    }
}

/// WebAssembly attributes
#[derive(Debug, Clone)]
pub struct WasmAttributes {
    attributes: AttributeMap,
}

impl WasmAttributes {
    /// Create a new builder
    pub fn builder() -> WasmAttributesBuilder {
        WasmAttributesBuilder::new()
    }

    /// Get all attributes
    pub fn as_map(&self) -> &AttributeMap {
        &self.attributes
    }

    /// Get a specific attribute
    pub fn get(&self, key: &str) -> Option<&AttributeValue> {
        self.attributes.get(key)
    }

    /// Get runtime name
    pub fn runtime_name(&self) -> Option<&str> {
        self.get(keys::WASM_RUNTIME_NAME).and_then(|v| v.as_str())
    }

    /// Get module name
    pub fn module_name(&self) -> Option<&str> {
        self.get(keys::WASM_MODULE_NAME).and_then(|v| v.as_str())
    }

    /// Get WASI version
    pub fn wasi_version(&self) -> Option<WasiVersion> {
        self.get(keys::WASM_RUNTIME_WASI_VERSION)
            .and_then(|v| v.as_str())
            .and_then(|s| match s {
                "preview1" => Some(WasiVersion::Preview1),
                "preview2" => Some(WasiVersion::Preview2),
                "preview3" => Some(WasiVersion::Preview3),
                "none" => Some(WasiVersion::None),
                _ => None,
            })
    }
}

/// Component Model attributes builder
#[derive(Debug, Default)]
pub struct ComponentAttributesBuilder {
    attributes: AttributeMap,
}

impl ComponentAttributesBuilder {
    /// Create a new builder
    pub fn new() -> Self {
        Self {
            attributes: AttributeMap::new(),
        }
    }

    /// Set component ID
    pub fn component_id(mut self, id: impl Into<String>) -> Self {
        self.attributes.insert(
            keys::WASM_COMPONENT_ID.into(),
            id.into().to_attribute_value(),
        );
        self
    }

    /// Set component version
    pub fn component_version(mut self, version: impl Into<String>) -> Self {
        self.attributes.insert(
            keys::WASM_COMPONENT_VERSION.into(),
            version.into().to_attribute_value(),
        );
        self
    }

    /// Set component package
    pub fn package(mut self, package: impl Into<String>) -> Self {
        self.attributes.insert(
            keys::WASM_COMPONENT_PACKAGE.into(),
            package.into().to_attribute_value(),
        );
        self
    }

    /// Set implemented interface
    pub fn interface(mut self, interface: impl Into<String>) -> Self {
        self.attributes.insert(
            keys::WASM_COMPONENT_INTERFACE.into(),
            interface.into().to_attribute_value(),
        );
        self
    }

    /// Build the attributes
    pub fn build(self) -> ComponentAttributes {
        ComponentAttributes {
            attributes: self.attributes,
        }
    }
}

/// Component Model attributes
#[derive(Debug, Clone)]
pub struct ComponentAttributes {
    attributes: AttributeMap,
}

impl ComponentAttributes {
    /// Create a new builder
    pub fn builder() -> ComponentAttributesBuilder {
        ComponentAttributesBuilder::new()
    }

    /// Get all attributes
    pub fn as_map(&self) -> &AttributeMap {
        &self.attributes
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_wasm_runtime_as_str() {
        assert_eq!(WasmRuntime::Wasmtime.as_str(), "wasmtime");
        assert_eq!(WasmRuntime::WasmCloud.as_str(), "wasmcloud");
        assert_eq!(WasmRuntime::Browser.as_str(), "browser");
    }

    #[test]
    fn test_wasi_version_as_str() {
        assert_eq!(WasiVersion::Preview1.as_str(), "preview1");
        assert_eq!(WasiVersion::Preview2.as_str(), "preview2");
        assert_eq!(WasiVersion::None.as_str(), "none");
    }

    #[test]
    fn test_wasm_attributes_builder() {
        let attrs = WasmAttributes::builder()
            .runtime_name("wasmtime")
            .runtime_version("15.0.0")
            .wasi_version(WasiVersion::Preview2)
            .module_name("my-component")
            .module_version("1.0.0")
            .module_language("rust")
            .memory_limit(134_217_728)
            .platform_type(WasmPlatform::Server)
            .platform_host("spin")
            .build();

        assert_eq!(attrs.runtime_name(), Some("wasmtime"));
        assert_eq!(attrs.module_name(), Some("my-component"));
        assert_eq!(attrs.wasi_version(), Some(WasiVersion::Preview2));
        assert!(attrs.get(keys::WASM_INSTANCE_MEMORY_LIMIT).is_some());
    }

    #[test]
    fn test_component_attributes_builder() {
        let attrs = ComponentAttributes::builder()
            .component_id("http-handler")
            .component_version("1.0.0")
            .package("example:http-handler")
            .interface("wasi:http/incoming-handler")
            .build();

        let map = attrs.as_map();
        assert!(map.contains_key(keys::WASM_COMPONENT_ID));
        assert!(map.contains_key(keys::WASM_COMPONENT_INTERFACE));
    }

    #[test]
    fn test_wasm_platform_as_str() {
        assert_eq!(WasmPlatform::Browser.as_str(), "browser");
        assert_eq!(WasmPlatform::Server.as_str(), "server");
        assert_eq!(WasmPlatform::Edge.as_str(), "edge");
    }
}
