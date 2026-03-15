//! # Container Semantic Conventions
//!
//! Implementation of OpenTelemetry Container Semantic Conventions v1.38.0
//! <https://opentelemetry.io/docs/specs/semconv/resource/container/>
//!
//! ## Supported Container Runtimes
//!
//! - **Docker**: Docker Engine and Docker Desktop
//! - **containerd**: Containerd runtime
//! - **CRI-O**: Kubernetes CRI runtime
//! - **Podman**: Podman container engine
//! - **rkt**: CoreOS Rocket (legacy)
//!
//! ## Kubernetes Integration
//!
//! - Pod name, UID, and labels
//! - Namespace
//! - Container name within pod
//! - ReplicaSet, Deployment, StatefulSet references
//!
//! ## Rust 1.92 Features
//!
//! - **Type-safe runtimes**: Enum-based container runtime definitions
//! - **Builder pattern**: Ergonomic container attribute construction
//! - **K8s integration**: Seamless Kubernetes attribute support
//!
//! ## Usage Example
//!
//! ```rust
//! use otlp::semantic_conventions::container::{
//!     ContainerAttributesBuilder, ContainerRuntime,
//! };
//!
//! let attrs = ContainerAttributesBuilder::new()
//!     .name("my-app")
//!     .container_id("abc123def456")
//!     .image_name("myapp:v1.2.3")
//!     .runtime(ContainerRuntime::Docker)
//!     .build()
//!     .unwrap();
//! ```

use super::common::{AttributeMap, AttributeValue, Result, SemanticConventionError};
use std::collections::HashMap;

/// Container runtimes
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ContainerRuntime {
    /// Docker Engine
    Docker,
    /// containerd
    Containerd,
    /// CRI-O
    Crio,
    /// Podman
    Podman,
    /// CoreOS Rocket (legacy)
    Rkt,
    /// containerd with CRI plugin
    CriContainerd,
    /// Windows Containers (Docker on Windows)
    DockerWindows,
    /// Mirantis Container Runtime
    Mirantis,
    /// Other runtime
    Other,
}

impl ContainerRuntime {
    /// Returns the string representation
    pub fn as_str(&self) -> &'static str {
        match self {
            ContainerRuntime::Docker => "docker",
            ContainerRuntime::Containerd => "containerd",
            ContainerRuntime::Crio => "cri-o",
            ContainerRuntime::Podman => "podman",
            ContainerRuntime::Rkt => "rkt",
            ContainerRuntime::CriContainerd => "cri-containerd",
            ContainerRuntime::DockerWindows => "docker-windows",
            ContainerRuntime::Mirantis => "mirantis",
            ContainerRuntime::Other => "other",
        }
    }
}

impl std::fmt::Display for ContainerRuntime {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.as_str())
    }
}

/// Container states
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ContainerState {
    /// Container is creating
    Creating,
    /// Container is running
    Running,
    /// Container is paused
    Paused,
    /// Container is restarting
    Restarting,
    /// Container has exited
    Exited,
    /// Container is dead
    Dead,
    /// Unknown state
    Unknown,
}

impl ContainerState {
    /// Returns the string representation
    pub fn as_str(&self) -> &'static str {
        match self {
            ContainerState::Creating => "creating",
            ContainerState::Running => "running",
            ContainerState::Paused => "paused",
            ContainerState::Restarting => "restarting",
            ContainerState::Exited => "exited",
            ContainerState::Dead => "dead",
            ContainerState::Unknown => "unknown",
        }
    }
}

/// Container attributes following OpenTelemetry semantic conventions
#[derive(Debug, Clone)]
pub struct ContainerAttributes {
    attributes: AttributeMap,
}

impl ContainerAttributes {
    /// Get all attributes as a map
    pub fn as_map(&self) -> &AttributeMap {
        &self.attributes
    }

    /// Get a specific attribute
    pub fn get(&self, key: &str) -> Option<&AttributeValue> {
        self.attributes.get(key)
    }
}

/// Builder for container attributes
#[derive(Debug, Default)]
pub struct ContainerAttributesBuilder {
    // Container identification
    name: Option<String>,
    container_id: Option<String>,
    runtime: Option<ContainerRuntime>,

    // Image information
    image_name: Option<String>,
    image_id: Option<String>,
    image_tag: Option<String>,
    image_repo_digests: Vec<String>,

    // Command information
    command: Option<String>,
    command_line: Option<String>,
    command_args: Vec<String>,

    // Resource limits
    cpu_limit: Option<f64>,
    memory_limit: Option<i64>,

    // State
    state: Option<ContainerState>,

    // Kubernetes specific
    k8s_pod_name: Option<String>,
    k8s_pod_uid: Option<String>,
    k8s_namespace: Option<String>,
    k8s_container_name: Option<String>,
    k8s_container_restart_count: Option<i32>,

    // Labels and annotations
    labels: HashMap<String, String>,
    annotations: HashMap<String, String>,

    // Custom attributes
    custom: HashMap<String, AttributeValue>,
}

impl ContainerAttributesBuilder {
    /// Create a new builder
    pub fn new() -> Self {
        Self::default()
    }

    /// Set container name
    pub fn name(mut self, name: impl Into<String>) -> Self {
        self.name = Some(name.into());
        self
    }

    /// Set container ID
    pub fn container_id(mut self, id: impl Into<String>) -> Self {
        self.container_id = Some(id.into());
        self
    }

    /// Set container runtime
    pub fn runtime(mut self, runtime: ContainerRuntime) -> Self {
        self.runtime = Some(runtime);
        self
    }

    /// Set image name (including tag if present)
    pub fn image_name(mut self, name: impl Into<String>) -> Self {
        self.image_name = Some(name.into());
        self
    }

    /// Set image ID (digest)
    pub fn image_id(mut self, id: impl Into<String>) -> Self {
        self.image_id = Some(id.into());
        self
    }

    /// Set image tag separately
    pub fn image_tag(mut self, tag: impl Into<String>) -> Self {
        self.image_tag = Some(tag.into());
        self
    }

    /// Add image repo digest
    pub fn add_image_repo_digest(mut self, digest: impl Into<String>) -> Self {
        self.image_repo_digests.push(digest.into());
        self
    }

    /// Set image repo digests
    pub fn image_repo_digests(mut self, digests: Vec<String>) -> Self {
        self.image_repo_digests = digests;
        self
    }

    /// Set container command
    pub fn command(mut self, cmd: impl Into<String>) -> Self {
        self.command = Some(cmd.into());
        self
    }

    /// Set full command line
    pub fn command_line(mut self, cmd_line: impl Into<String>) -> Self {
        self.command_line = Some(cmd_line.into());
        self
    }

    /// Add command argument
    pub fn add_command_arg(mut self, arg: impl Into<String>) -> Self {
        self.command_args.push(arg.into());
        self
    }

    /// Set command arguments
    pub fn command_args(mut self, args: Vec<String>) -> Self {
        self.command_args = args;
        self
    }

    /// Set CPU limit (cores)
    pub fn cpu_limit(mut self, cores: f64) -> Self {
        self.cpu_limit = Some(cores);
        self
    }

    /// Set memory limit (bytes)
    pub fn memory_limit(mut self, bytes: i64) -> Self {
        self.memory_limit = Some(bytes);
        self
    }

    /// Set container state
    pub fn state(mut self, state: ContainerState) -> Self {
        self.state = Some(state);
        self
    }

    /// Set Kubernetes pod name
    pub fn k8s_pod_name(mut self, name: impl Into<String>) -> Self {
        self.k8s_pod_name = Some(name.into());
        self
    }

    /// Set Kubernetes pod UID
    pub fn k8s_pod_uid(mut self, uid: impl Into<String>) -> Self {
        self.k8s_pod_uid = Some(uid.into());
        self
    }

    /// Set Kubernetes namespace
    pub fn k8s_namespace(mut self, namespace: impl Into<String>) -> Self {
        self.k8s_namespace = Some(namespace.into());
        self
    }

    /// Set Kubernetes container name (within pod)
    pub fn k8s_container_name(mut self, name: impl Into<String>) -> Self {
        self.k8s_container_name = Some(name.into());
        self
    }

    /// Set Kubernetes container restart count
    pub fn k8s_container_restart_count(mut self, count: i32) -> Self {
        self.k8s_container_restart_count = Some(count);
        self
    }

    /// Add container label
    pub fn label(mut self, key: impl Into<String>, value: impl Into<String>) -> Self {
        self.labels.insert(key.into(), value.into());
        self
    }

    /// Set container labels
    pub fn labels(mut self, labels: HashMap<String, String>) -> Self {
        self.labels = labels;
        self
    }

    /// Add annotation
    pub fn annotation(mut self, key: impl Into<String>, value: impl Into<String>) -> Self {
        self.annotations.insert(key.into(), value.into());
        self
    }

    /// Set annotations
    pub fn annotations(mut self, annotations: HashMap<String, String>) -> Self {
        self.annotations = annotations;
        self
    }

    /// Add a custom attribute
    pub fn custom_attribute(mut self, key: impl Into<String>, value: AttributeValue) -> Self {
        self.custom.insert(key.into(), value);
        self
    }

    /// Build the container attributes
    pub fn build(self) -> Result<ContainerAttributes> {
        // Container name is required
        let name = self.name.ok_or_else(|| {
            SemanticConventionError::MissingRequired("container.name".to_string())
        })?;

        let mut attributes = AttributeMap::new();

        // Required
        attributes.insert(
            "container.name".to_string(),
            AttributeValue::String(name),
        );

        // Optional
        if let Some(id) = self.container_id {
            attributes.insert(
                "container.id".to_string(),
                AttributeValue::String(id),
            );
        }

        if let Some(runtime) = self.runtime {
            attributes.insert(
                "container.runtime".to_string(),
                AttributeValue::String(runtime.as_str().to_string()),
            );
        }

        if let Some(image_name) = self.image_name {
            attributes.insert(
                "container.image.name".to_string(),
                AttributeValue::String(image_name),
            );
        }

        if let Some(image_id) = self.image_id {
            attributes.insert(
                "container.image.id".to_string(),
                AttributeValue::String(image_id),
            );
        }

        if let Some(tag) = self.image_tag {
            attributes.insert(
                "container.image.tag".to_string(),
                AttributeValue::String(tag),
            );
        }

        if !self.image_repo_digests.is_empty() {
            attributes.insert(
                "container.image.repo_digests".to_string(),
                AttributeValue::Array(
                    self.image_repo_digests
                        .into_iter()
                        .map(AttributeValue::String)
                        .collect(),
                ),
            );
        }

        if let Some(cmd) = self.command {
            attributes.insert(
                "container.command".to_string(),
                AttributeValue::String(cmd),
            );
        }

        if let Some(cmd_line) = self.command_line {
            attributes.insert(
                "container.command_line".to_string(),
                AttributeValue::String(cmd_line),
            );
        }

        if !self.command_args.is_empty() {
            attributes.insert(
                "container.command_args".to_string(),
                AttributeValue::Array(
                    self.command_args
                        .into_iter()
                        .map(AttributeValue::String)
                        .collect(),
                ),
            );
        }

        if let Some(cpu) = self.cpu_limit {
            attributes.insert(
                "container.cpu.limit".to_string(),
                AttributeValue::Double(cpu),
            );
        }

        if let Some(memory) = self.memory_limit {
            attributes.insert(
                "container.memory.limit".to_string(),
                AttributeValue::Int(memory),
            );
        }

        if let Some(state) = self.state {
            attributes.insert(
                "container.state".to_string(),
                AttributeValue::String(state.as_str().to_string()),
            );
        }

        // Kubernetes attributes
        if let Some(pod_name) = self.k8s_pod_name {
            attributes.insert(
                "k8s.pod.name".to_string(),
                AttributeValue::String(pod_name),
            );
        }

        if let Some(pod_uid) = self.k8s_pod_uid {
            attributes.insert(
                "k8s.pod.uid".to_string(),
                AttributeValue::String(pod_uid),
            );
        }

        if let Some(namespace) = self.k8s_namespace {
            attributes.insert(
                "k8s.namespace.name".to_string(),
                AttributeValue::String(namespace),
            );
        }

        if let Some(container_name) = self.k8s_container_name {
            attributes.insert(
                "k8s.container.name".to_string(),
                AttributeValue::String(container_name),
            );
        }

        if let Some(restart_count) = self.k8s_container_restart_count {
            attributes.insert(
                "k8s.container.restart_count".to_string(),
                AttributeValue::Int(restart_count as i64),
            );
        }

        // Labels
        for (key, value) in self.labels {
            attributes.insert(
                format!("container.label.{}", key),
                AttributeValue::String(value),
            );
        }

        // Annotations (if any, usually K8s-specific)
        for (key, value) in self.annotations {
            attributes.insert(
                format!("k8s.container.annotation.{}", key),
                AttributeValue::String(value),
            );
        }

        // Add custom attributes
        attributes.extend(self.custom);

        Ok(ContainerAttributes { attributes })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_container_runtime() {
        assert_eq!(ContainerRuntime::Docker.as_str(), "docker");
        assert_eq!(ContainerRuntime::Containerd.as_str(), "containerd");
        assert_eq!(ContainerRuntime::Podman.as_str(), "podman");
        assert_eq!(ContainerRuntime::Crio.as_str(), "cri-o");
    }

    #[test]
    fn test_container_state() {
        assert_eq!(ContainerState::Running.as_str(), "running");
        assert_eq!(ContainerState::Exited.as_str(), "exited");
        assert_eq!(ContainerState::Dead.as_str(), "dead");
    }

    #[test]
    fn test_container_attributes_builder_minimal() {
        let attrs = ContainerAttributesBuilder::new()
            .name("my-container")
            .build()
            .unwrap();

        assert_eq!(
            attrs.get("container.name"),
            Some(&AttributeValue::String("my-container".to_string()))
        );
    }

    #[test]
    fn test_container_attributes_builder_full() {
        let attrs = ContainerAttributesBuilder::new()
            .name("web-server")
            .container_id("abc123def456789")
            .runtime(ContainerRuntime::Docker)
            .image_name("nginx:latest")
            .image_id("sha256:abc123")
            .image_tag("latest")
            .command("nginx")
            .add_command_arg("-g")
            .add_command_arg("daemon off;")
            .cpu_limit(2.0)
            .memory_limit(2147483648)
            .state(ContainerState::Running)
            .build()
            .unwrap();

        assert_eq!(
            attrs.get("container.id"),
            Some(&AttributeValue::String("abc123def456789".to_string()))
        );
        assert_eq!(
            attrs.get("container.runtime"),
            Some(&AttributeValue::String("docker".to_string()))
        );
        assert_eq!(
            attrs.get("container.image.name"),
            Some(&AttributeValue::String("nginx:latest".to_string()))
        );
        assert_eq!(
            attrs.get("container.cpu.limit"),
            Some(&AttributeValue::Double(2.0))
        );
        assert_eq!(
            attrs.get("container.memory.limit"),
            Some(&AttributeValue::Int(2147483648))
        );
        assert_eq!(
            attrs.get("container.state"),
            Some(&AttributeValue::String("running".to_string()))
        );
    }

    #[test]
    fn test_container_kubernetes() {
        let attrs = ContainerAttributesBuilder::new()
            .name("main-container")
            .container_id("container789")
            .k8s_pod_name("my-pod-123")
            .k8s_pod_uid("pod-uid-abc")
            .k8s_namespace("production")
            .k8s_container_name("main")
            .k8s_container_restart_count(2)
            .build()
            .unwrap();

        assert_eq!(
            attrs.get("k8s.pod.name"),
            Some(&AttributeValue::String("my-pod-123".to_string()))
        );
        assert_eq!(
            attrs.get("k8s.pod.uid"),
            Some(&AttributeValue::String("pod-uid-abc".to_string()))
        );
        assert_eq!(
            attrs.get("k8s.namespace.name"),
            Some(&AttributeValue::String("production".to_string()))
        );
        assert_eq!(
            attrs.get("k8s.container.name"),
            Some(&AttributeValue::String("main".to_string()))
        );
        assert_eq!(
            attrs.get("k8s.container.restart_count"),
            Some(&AttributeValue::Int(2))
        );
    }

    #[test]
    fn test_container_labels() {
        let attrs = ContainerAttributesBuilder::new()
            .name("labeled-container")
            .label("app", "web")
            .label("env", "production")
            .label("version", "v1.0.0")
            .build()
            .unwrap();

        assert_eq!(
            attrs.get("container.label.app"),
            Some(&AttributeValue::String("web".to_string()))
        );
        assert_eq!(
            attrs.get("container.label.env"),
            Some(&AttributeValue::String("production".to_string()))
        );
        assert_eq!(
            attrs.get("container.label.version"),
            Some(&AttributeValue::String("v1.0.0".to_string()))
        );
    }

    #[test]
    fn test_container_image_repo_digests() {
        let attrs = ContainerAttributesBuilder::new()
            .name("secure-container")
            .add_image_repo_digest("nginx@sha256:abc123...")
            .add_image_repo_digest("nginx@sha256:def456...")
            .build()
            .unwrap();

        let digests = attrs.get("container.image.repo_digests");
        assert!(digests.is_some());
        if let Some(AttributeValue::Array(arr)) = digests {
            assert_eq!(arr.len(), 2);
        }
    }

    #[test]
    fn test_container_attributes_builder_missing_required() {
        let result = ContainerAttributesBuilder::new().build();

        assert!(result.is_err());
        match result {
            Err(SemanticConventionError::MissingRequired(field)) => {
                assert_eq!(field, "container.name");
            }
            _ => panic!("Expected MissingRequired error"),
        }
    }

    #[test]
    fn test_container_custom_attributes() {
        let attrs = ContainerAttributesBuilder::new()
            .name("custom-container")
            .custom_attribute("custom.health", AttributeValue::String("healthy".to_string()))
            .custom_attribute("custom.uptime", AttributeValue::Int(3600))
            .build()
            .unwrap();

        assert_eq!(
            attrs.get("custom.health"),
            Some(&AttributeValue::String("healthy".to_string()))
        );
        assert_eq!(
            attrs.get("custom.uptime"),
            Some(&AttributeValue::Int(3600))
        );
    }

    #[test]
    fn test_all_container_runtimes() {
        let runtimes = vec![
            ContainerRuntime::Docker,
            ContainerRuntime::Containerd,
            ContainerRuntime::Podman,
            ContainerRuntime::Crio,
            ContainerRuntime::Rkt,
        ];

        for runtime in runtimes {
            let attrs = ContainerAttributesBuilder::new()
                .name("test-container")
                .runtime(runtime)
                .build()
                .unwrap();

            assert!(
                attrs.get("container.runtime").is_some(),
                "container.runtime should be present"
            );
        }
    }
}
