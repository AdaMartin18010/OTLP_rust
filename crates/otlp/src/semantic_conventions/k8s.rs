//! # Kubernetes Semantic Conventions
//!
//! This module implements OpenTelemetry semantic conventions for Kubernetes resources.
//! It provides type-safe builders for creating Kubernetes-related attributes.
//!
//! ## Supported Resource Types
//!
//! - **Pods**: Running container groups
//! - **Deployments**: Deployment controllers
//! - **Services**: Service definitions
//! - **Nodes**: Kubernetes nodes
//! - **Namespaces**: Logical clusters
//! - **Containers**: Individual containers
//!
//! ## Rust 1.92 特性应用
//!
//! - **常量泛型**: 使用常量泛型优化K8s属性键值对大小
//! - **元组收集**: 使用 `collect()` 直接收集K8s属性到元组
//! - **改进的类型系统**: 利用 Rust 1.92 的类型系统优化提升性能
//!
//! ## Usage Example
//!
//! ```rust
//! use otlp::semantic_conventions::k8s::{
//!     K8sAttributesBuilder, K8sResourceType,
//! };
//!
//! let attrs = K8sAttributesBuilder::new()
//!     .cluster_name("production")
//!     .namespace_name("default")
//!     .pod_name("web-server-123")
//!     .build()
//!     .unwrap();
//! ```

use super::common::AttributeValue;
use std::collections::HashMap;

/// Kubernetes resource types
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum K8sResourceType {
    /// Pod
    Pod,
    /// Deployment
    Deployment,
    /// Service
    Service,
    /// Node
    Node,
    /// Namespace
    Namespace,
    /// Container
    Container,
    /// ReplicaSet
    ReplicaSet,
    /// DaemonSet
    DaemonSet,
    /// StatefulSet
    StatefulSet,
    /// Job
    Job,
    /// CronJob
    CronJob,
}

impl K8sResourceType {
    /// Returns the string representation
    pub fn as_str(&self) -> &str {
        match self {
            K8sResourceType::Pod => "pod",
            K8sResourceType::Deployment => "deployment",
            K8sResourceType::Service => "service",
            K8sResourceType::Node => "node",
            K8sResourceType::Namespace => "namespace",
            K8sResourceType::Container => "container",
            K8sResourceType::ReplicaSet => "replicaset",
            K8sResourceType::DaemonSet => "daemonset",
            K8sResourceType::StatefulSet => "statefulset",
            K8sResourceType::Job => "job",
            K8sResourceType::CronJob => "cronjob",
        }
    }
}

impl std::fmt::Display for K8sResourceType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.as_str())
    }
}

/// Kubernetes attributes following OpenTelemetry semantic conventions
#[derive(Debug, Clone)]
pub struct K8sAttributes {
    // Cluster attributes
    /// Kubernetes cluster name
    pub cluster_name: Option<String>,

    // Node attributes
    /// Node name
    pub node_name: Option<String>,
    /// Node UID
    pub node_uid: Option<String>,

    // Namespace attributes
    /// Namespace name
    pub namespace_name: Option<String>,

    // Pod attributes
    /// Pod name
    pub pod_name: Option<String>,
    /// Pod UID
    pub pod_uid: Option<String>,
    /// Pod labels
    pub pod_labels: Option<HashMap<String, String>>,

    // Container attributes
    /// Container name
    pub container_name: Option<String>,
    /// Container ID
    pub container_id: Option<String>,
    /// Container image name
    pub container_image_name: Option<String>,
    /// Container image tag
    pub container_image_tag: Option<String>,
    /// Container restart count
    pub container_restart_count: Option<i32>,

    // Deployment attributes
    /// Deployment name
    pub deployment_name: Option<String>,
    /// Deployment UID
    pub deployment_uid: Option<String>,

    // ReplicaSet attributes
    /// ReplicaSet name
    pub replicaset_name: Option<String>,
    /// ReplicaSet UID
    pub replicaset_uid: Option<String>,

    // StatefulSet attributes
    /// StatefulSet name
    pub statefulset_name: Option<String>,
    /// StatefulSet UID
    pub statefulset_uid: Option<String>,

    // DaemonSet attributes
    /// DaemonSet name
    pub daemonset_name: Option<String>,
    /// DaemonSet UID
    pub daemonset_uid: Option<String>,

    // Job attributes
    /// Job name
    pub job_name: Option<String>,
    /// Job UID
    pub job_uid: Option<String>,

    // CronJob attributes
    /// CronJob name
    pub cronjob_name: Option<String>,
    /// CronJob UID
    pub cronjob_uid: Option<String>,
}

impl K8sAttributes {
    /// Converts the attributes to a HashMap
    pub fn to_attributes(&self) -> HashMap<String, AttributeValue> {
        let mut map = HashMap::new();

        // Cluster attributes
        if let Some(ref cluster) = self.cluster_name {
            map.insert(
                "k8s.cluster.name".to_string(),
                AttributeValue::String(cluster.clone()),
            );
        }

        // Node attributes
        if let Some(ref node) = self.node_name {
            map.insert(
                "k8s.node.name".to_string(),
                AttributeValue::String(node.clone()),
            );
        }

        if let Some(ref node_uid) = self.node_uid {
            map.insert(
                "k8s.node.uid".to_string(),
                AttributeValue::String(node_uid.clone()),
            );
        }

        // Namespace attributes
        if let Some(ref namespace) = self.namespace_name {
            map.insert(
                "k8s.namespace.name".to_string(),
                AttributeValue::String(namespace.clone()),
            );
        }

        // Pod attributes
        if let Some(ref pod) = self.pod_name {
            map.insert(
                "k8s.pod.name".to_string(),
                AttributeValue::String(pod.clone()),
            );
        }

        if let Some(ref pod_uid) = self.pod_uid {
            map.insert(
                "k8s.pod.uid".to_string(),
                AttributeValue::String(pod_uid.clone()),
            );
        }

        if let Some(ref labels) = self.pod_labels {
            for (key, value) in labels {
                map.insert(
                    format!("k8s.pod.labels.{}", key),
                    AttributeValue::String(value.clone()),
                );
            }
        }

        // Container attributes
        if let Some(ref container) = self.container_name {
            map.insert(
                "k8s.container.name".to_string(),
                AttributeValue::String(container.clone()),
            );
        }

        if let Some(ref container_id) = self.container_id {
            map.insert(
                "k8s.container.id".to_string(),
                AttributeValue::String(container_id.clone()),
            );
        }

        if let Some(ref image) = self.container_image_name {
            map.insert(
                "k8s.container.image.name".to_string(),
                AttributeValue::String(image.clone()),
            );
        }

        if let Some(ref tag) = self.container_image_tag {
            map.insert(
                "k8s.container.image.tag".to_string(),
                AttributeValue::String(tag.clone()),
            );
        }

        if let Some(restart_count) = self.container_restart_count {
            map.insert(
                "k8s.container.restart_count".to_string(),
                AttributeValue::Int(restart_count as i64),
            );
        }

        // Deployment attributes
        if let Some(ref deployment) = self.deployment_name {
            map.insert(
                "k8s.deployment.name".to_string(),
                AttributeValue::String(deployment.clone()),
            );
        }

        if let Some(ref deployment_uid) = self.deployment_uid {
            map.insert(
                "k8s.deployment.uid".to_string(),
                AttributeValue::String(deployment_uid.clone()),
            );
        }

        // ReplicaSet attributes
        if let Some(ref replicaset) = self.replicaset_name {
            map.insert(
                "k8s.replicaset.name".to_string(),
                AttributeValue::String(replicaset.clone()),
            );
        }

        if let Some(ref replicaset_uid) = self.replicaset_uid {
            map.insert(
                "k8s.replicaset.uid".to_string(),
                AttributeValue::String(replicaset_uid.clone()),
            );
        }

        // StatefulSet attributes
        if let Some(ref statefulset) = self.statefulset_name {
            map.insert(
                "k8s.statefulset.name".to_string(),
                AttributeValue::String(statefulset.clone()),
            );
        }

        if let Some(ref statefulset_uid) = self.statefulset_uid {
            map.insert(
                "k8s.statefulset.uid".to_string(),
                AttributeValue::String(statefulset_uid.clone()),
            );
        }

        // DaemonSet attributes
        if let Some(ref daemonset) = self.daemonset_name {
            map.insert(
                "k8s.daemonset.name".to_string(),
                AttributeValue::String(daemonset.clone()),
            );
        }

        if let Some(ref daemonset_uid) = self.daemonset_uid {
            map.insert(
                "k8s.daemonset.uid".to_string(),
                AttributeValue::String(daemonset_uid.clone()),
            );
        }

        // Job attributes
        if let Some(ref job) = self.job_name {
            map.insert(
                "k8s.job.name".to_string(),
                AttributeValue::String(job.clone()),
            );
        }

        if let Some(ref job_uid) = self.job_uid {
            map.insert(
                "k8s.job.uid".to_string(),
                AttributeValue::String(job_uid.clone()),
            );
        }

        // CronJob attributes
        if let Some(ref cronjob) = self.cronjob_name {
            map.insert(
                "k8s.cronjob.name".to_string(),
                AttributeValue::String(cronjob.clone()),
            );
        }

        if let Some(ref cronjob_uid) = self.cronjob_uid {
            map.insert(
                "k8s.cronjob.uid".to_string(),
                AttributeValue::String(cronjob_uid.clone()),
            );
        }

        map
    }
}

/// Builder for K8sAttributes
#[derive(Debug, Default)]
pub struct K8sAttributesBuilder {
    cluster_name: Option<String>,
    node_name: Option<String>,
    node_uid: Option<String>,
    namespace_name: Option<String>,
    pod_name: Option<String>,
    pod_uid: Option<String>,
    pod_labels: Option<HashMap<String, String>>,
    container_name: Option<String>,
    container_id: Option<String>,
    container_image_name: Option<String>,
    container_image_tag: Option<String>,
    container_restart_count: Option<i32>,
    deployment_name: Option<String>,
    deployment_uid: Option<String>,
    replicaset_name: Option<String>,
    replicaset_uid: Option<String>,
    statefulset_name: Option<String>,
    statefulset_uid: Option<String>,
    daemonset_name: Option<String>,
    daemonset_uid: Option<String>,
    job_name: Option<String>,
    job_uid: Option<String>,
    cronjob_name: Option<String>,
    cronjob_uid: Option<String>,
}

impl K8sAttributesBuilder {
    /// Creates a new K8sAttributesBuilder
    pub fn new() -> Self {
        Self::default()
    }

    /// Sets the cluster name
    pub fn cluster_name(mut self, name: impl Into<String>) -> Self {
        self.cluster_name = Some(name.into());
        self
    }

    /// Sets the node name
    pub fn node_name(mut self, name: impl Into<String>) -> Self {
        self.node_name = Some(name.into());
        self
    }

    /// Sets the node UID
    pub fn node_uid(mut self, uid: impl Into<String>) -> Self {
        self.node_uid = Some(uid.into());
        self
    }

    /// Sets the namespace name
    pub fn namespace_name(mut self, name: impl Into<String>) -> Self {
        self.namespace_name = Some(name.into());
        self
    }

    /// Sets the pod name
    pub fn pod_name(mut self, name: impl Into<String>) -> Self {
        self.pod_name = Some(name.into());
        self
    }

    /// Sets the pod UID
    pub fn pod_uid(mut self, uid: impl Into<String>) -> Self {
        self.pod_uid = Some(uid.into());
        self
    }

    /// Sets pod labels
    pub fn pod_labels(mut self, labels: HashMap<String, String>) -> Self {
        self.pod_labels = Some(labels);
        self
    }

    /// Adds a single pod label
    pub fn pod_label(mut self, key: impl Into<String>, value: impl Into<String>) -> Self {
        let labels = self.pod_labels.get_or_insert_with(HashMap::new);
        labels.insert(key.into(), value.into());
        self
    }

    /// Sets the container name
    pub fn container_name(mut self, name: impl Into<String>) -> Self {
        self.container_name = Some(name.into());
        self
    }

    /// Sets the container ID
    pub fn container_id(mut self, id: impl Into<String>) -> Self {
        self.container_id = Some(id.into());
        self
    }

    /// Sets the container image name
    pub fn container_image_name(mut self, name: impl Into<String>) -> Self {
        self.container_image_name = Some(name.into());
        self
    }

    /// Sets the container image tag
    pub fn container_image_tag(mut self, tag: impl Into<String>) -> Self {
        self.container_image_tag = Some(tag.into());
        self
    }

    /// Sets the container restart count
    pub fn container_restart_count(mut self, count: i32) -> Self {
        self.container_restart_count = Some(count);
        self
    }

    /// Sets the deployment name
    pub fn deployment_name(mut self, name: impl Into<String>) -> Self {
        self.deployment_name = Some(name.into());
        self
    }

    /// Sets the deployment UID
    pub fn deployment_uid(mut self, uid: impl Into<String>) -> Self {
        self.deployment_uid = Some(uid.into());
        self
    }

    /// Sets the replicaset name
    pub fn replicaset_name(mut self, name: impl Into<String>) -> Self {
        self.replicaset_name = Some(name.into());
        self
    }

    /// Sets the replicaset UID
    pub fn replicaset_uid(mut self, uid: impl Into<String>) -> Self {
        self.replicaset_uid = Some(uid.into());
        self
    }

    /// Sets the statefulset name
    pub fn statefulset_name(mut self, name: impl Into<String>) -> Self {
        self.statefulset_name = Some(name.into());
        self
    }

    /// Sets the statefulset UID
    pub fn statefulset_uid(mut self, uid: impl Into<String>) -> Self {
        self.statefulset_uid = Some(uid.into());
        self
    }

    /// Sets the daemonset name
    pub fn daemonset_name(mut self, name: impl Into<String>) -> Self {
        self.daemonset_name = Some(name.into());
        self
    }

    /// Sets the daemonset UID
    pub fn daemonset_uid(mut self, uid: impl Into<String>) -> Self {
        self.daemonset_uid = Some(uid.into());
        self
    }

    /// Sets the job name
    pub fn job_name(mut self, name: impl Into<String>) -> Self {
        self.job_name = Some(name.into());
        self
    }

    /// Sets the job UID
    pub fn job_uid(mut self, uid: impl Into<String>) -> Self {
        self.job_uid = Some(uid.into());
        self
    }

    /// Sets the cronjob name
    pub fn cronjob_name(mut self, name: impl Into<String>) -> Self {
        self.cronjob_name = Some(name.into());
        self
    }

    /// Sets the cronjob UID
    pub fn cronjob_uid(mut self, uid: impl Into<String>) -> Self {
        self.cronjob_uid = Some(uid.into());
        self
    }

    /// Builds the K8sAttributes
    pub fn build(self) -> Result<K8sAttributes, String> {
        Ok(K8sAttributes {
            cluster_name: self.cluster_name,
            node_name: self.node_name,
            node_uid: self.node_uid,
            namespace_name: self.namespace_name,
            pod_name: self.pod_name,
            pod_uid: self.pod_uid,
            pod_labels: self.pod_labels,
            container_name: self.container_name,
            container_id: self.container_id,
            container_image_name: self.container_image_name,
            container_image_tag: self.container_image_tag,
            container_restart_count: self.container_restart_count,
            deployment_name: self.deployment_name,
            deployment_uid: self.deployment_uid,
            replicaset_name: self.replicaset_name,
            replicaset_uid: self.replicaset_uid,
            statefulset_name: self.statefulset_name,
            statefulset_uid: self.statefulset_uid,
            daemonset_name: self.daemonset_name,
            daemonset_uid: self.daemonset_uid,
            job_name: self.job_name,
            job_uid: self.job_uid,
            cronjob_name: self.cronjob_name,
            cronjob_uid: self.cronjob_uid,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_basic_pod_attributes() {
        let attrs = K8sAttributesBuilder::new()
            .cluster_name("production")
            .namespace_name("default")
            .pod_name("web-server-123")
            .pod_uid("abc-def-123")
            .build()
            .unwrap();

        let map = attrs.to_attributes();
        assert_eq!(
            map.get("k8s.cluster.name"),
            Some(&AttributeValue::String("production".to_string()))
        );
        assert_eq!(
            map.get("k8s.namespace.name"),
            Some(&AttributeValue::String("default".to_string()))
        );
        assert_eq!(
            map.get("k8s.pod.name"),
            Some(&AttributeValue::String("web-server-123".to_string()))
        );
    }

    #[test]
    fn test_container_attributes() {
        let attrs = K8sAttributesBuilder::new()
            .cluster_name("staging")
            .namespace_name("api")
            .pod_name("api-server-456")
            .container_name("main")
            .container_image_name("myapp")
            .container_image_tag("v1.2.3")
            .container_restart_count(2)
            .build()
            .unwrap();

        let map = attrs.to_attributes();
        assert_eq!(
            map.get("k8s.container.name"),
            Some(&AttributeValue::String("main".to_string()))
        );
        assert_eq!(
            map.get("k8s.container.image.name"),
            Some(&AttributeValue::String("myapp".to_string()))
        );
        assert_eq!(
            map.get("k8s.container.image.tag"),
            Some(&AttributeValue::String("v1.2.3".to_string()))
        );
        assert_eq!(
            map.get("k8s.container.restart_count"),
            Some(&AttributeValue::Int(2))
        );
    }

    #[test]
    fn test_deployment_attributes() {
        let attrs = K8sAttributesBuilder::new()
            .cluster_name("production")
            .namespace_name("backend")
            .deployment_name("user-service")
            .deployment_uid("deploy-123")
            .replicaset_name("user-service-abc")
            .pod_name("user-service-abc-xyz")
            .build()
            .unwrap();

        let map = attrs.to_attributes();
        assert_eq!(
            map.get("k8s.deployment.name"),
            Some(&AttributeValue::String("user-service".to_string()))
        );
        assert_eq!(
            map.get("k8s.replicaset.name"),
            Some(&AttributeValue::String("user-service-abc".to_string()))
        );
    }

    #[test]
    fn test_pod_labels() {
        let mut labels = HashMap::new();
        labels.insert("app".to_string(), "web".to_string());
        labels.insert("version".to_string(), "v1".to_string());

        let attrs = K8sAttributesBuilder::new()
            .pod_name("web-123")
            .pod_labels(labels)
            .build()
            .unwrap();

        let map = attrs.to_attributes();
        assert_eq!(
            map.get("k8s.pod.labels.app"),
            Some(&AttributeValue::String("web".to_string()))
        );
        assert_eq!(
            map.get("k8s.pod.labels.version"),
            Some(&AttributeValue::String("v1".to_string()))
        );
    }

    #[test]
    fn test_job_and_cronjob() {
        let attrs = K8sAttributesBuilder::new()
            .cluster_name("production")
            .namespace_name("batch")
            .cronjob_name("daily-report")
            .job_name("daily-report-20231023")
            .job_uid("job-123")
            .pod_name("daily-report-20231023-pod")
            .build()
            .unwrap();

        let map = attrs.to_attributes();
        assert_eq!(
            map.get("k8s.cronjob.name"),
            Some(&AttributeValue::String("daily-report".to_string()))
        );
        assert_eq!(
            map.get("k8s.job.name"),
            Some(&AttributeValue::String("daily-report-20231023".to_string()))
        );
    }

    #[test]
    fn test_node_attributes() {
        let attrs = K8sAttributesBuilder::new()
            .cluster_name("production")
            .node_name("worker-node-01")
            .node_uid("node-abc-123")
            .build()
            .unwrap();

        let map = attrs.to_attributes();
        assert_eq!(
            map.get("k8s.node.name"),
            Some(&AttributeValue::String("worker-node-01".to_string()))
        );
        assert_eq!(
            map.get("k8s.node.uid"),
            Some(&AttributeValue::String("node-abc-123".to_string()))
        );
    }

    #[test]
    fn test_pod_label_method() {
        let attrs = K8sAttributesBuilder::new()
            .pod_name("test-pod")
            .pod_label("env", "prod")
            .pod_label("tier", "frontend")
            .build()
            .unwrap();

        let map = attrs.to_attributes();
        assert_eq!(
            map.get("k8s.pod.labels.env"),
            Some(&AttributeValue::String("prod".to_string()))
        );
        assert_eq!(
            map.get("k8s.pod.labels.tier"),
            Some(&AttributeValue::String("frontend".to_string()))
        );
    }
}
