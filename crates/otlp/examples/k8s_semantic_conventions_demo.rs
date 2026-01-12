//! Kubernetes Semantic Conventions Demo
//!
//! This example demonstrates the usage of Kubernetes semantic conventions
//! for various K8s resources (Pods, Deployments, Services, Nodes, etc.).

use otlp::semantic_conventions::k8s::K8sAttributesBuilder;
use std::collections::HashMap;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    println!("☸️  OpenTelemetry Kubernetes Semantic Conventions Demo\n");
    println!("============================================================\n");

    // Demo 1: Basic Pod Attributes
    println!("📊 Demo 1: Basic Pod Attributes");
    let pod_attrs = K8sAttributesBuilder::new()
        .cluster_name("production")
        .namespace_name("default")
        .pod_name("web-server-123")
        .pod_uid("abc-def-123-456")
        .build()?;

    println!("  ✅ Created pod attributes:");
    for (key, value) in pod_attrs.to_attributes() {
        println!("     - {}: {}", key, value);
    }
    println!("\n============================================================\n");

    // Demo 2: Container in Pod
    println!("📊 Demo 2: Container in Pod");
    let container_attrs = K8sAttributesBuilder::new()
        .cluster_name("production")
        .namespace_name("api")
        .pod_name("api-server-456")
        .pod_uid("pod-789-abc")
        .container_name("main")
        .container_id("containerd://abc123def456")
        .container_image_name("myregistry.io/api-server")
        .container_image_tag("v1.2.3")
        .container_restart_count(2)
        .build()?;

    println!("  ✅ Created container attributes:");
    for (key, value) in container_attrs.to_attributes() {
        println!("     - {}: {}", key, value);
    }
    println!("\n============================================================\n");

    // Demo 3: Deployment with ReplicaSet
    println!("📊 Demo 3: Deployment with ReplicaSet");
    let deployment_attrs = K8sAttributesBuilder::new()
        .cluster_name("production")
        .namespace_name("backend")
        .deployment_name("user-service")
        .deployment_uid("deploy-abc-123")
        .replicaset_name("user-service-abc123")
        .replicaset_uid("rs-def-456")
        .pod_name("user-service-abc123-xyz789")
        .pod_uid("pod-ghi-789")
        .build()?;

    println!("  ✅ Created deployment attributes:");
    for (key, value) in deployment_attrs.to_attributes() {
        println!("     - {}: {}", key, value);
    }
    println!("\n============================================================\n");

    // Demo 4: Pod with Labels
    println!("📊 Demo 4: Pod with Labels");
    let mut labels = HashMap::new();
    labels.insert("app".to_string(), "web".to_string());
    labels.insert("version".to_string(), "v1".to_string());
    labels.insert("env".to_string(), "production".to_string());

    let labeled_pod_attrs = K8sAttributesBuilder::new()
        .cluster_name("production")
        .namespace_name("frontend")
        .pod_name("web-frontend-123")
        .pod_labels(labels)
        .build()?;

    println!("  ✅ Created pod with labels:");
    for (key, value) in labeled_pod_attrs.to_attributes() {
        println!("     - {}: {}", key, value);
    }
    println!("\n============================================================\n");

    // Demo 5: StatefulSet
    println!("📊 Demo 5: StatefulSet");
    let statefulset_attrs = K8sAttributesBuilder::new()
        .cluster_name("production")
        .namespace_name("database")
        .statefulset_name("postgres")
        .statefulset_uid("sts-abc-123")
        .pod_name("postgres-0")
        .pod_uid("pod-postgres-0")
        .container_name("postgres")
        .container_image_name("postgres")
        .container_image_tag("14.5")
        .build()?;

    println!("  ✅ Created statefulset attributes:");
    for (key, value) in statefulset_attrs.to_attributes() {
        println!("     - {}: {}", key, value);
    }
    println!("\n============================================================\n");

    // Demo 6: DaemonSet
    println!("📊 Demo 6: DaemonSet");
    let daemonset_attrs = K8sAttributesBuilder::new()
        .cluster_name("production")
        .namespace_name("kube-system")
        .daemonset_name("fluentd")
        .daemonset_uid("ds-abc-123")
        .node_name("worker-node-01")
        .pod_name("fluentd-abc12")
        .build()?;

    println!("  ✅ Created daemonset attributes:");
    for (key, value) in daemonset_attrs.to_attributes() {
        println!("     - {}: {}", key, value);
    }
    println!("\n============================================================\n");

    // Demo 7: CronJob and Job
    println!("📊 Demo 7: CronJob and Job");
    let cronjob_attrs = K8sAttributesBuilder::new()
        .cluster_name("production")
        .namespace_name("batch")
        .cronjob_name("daily-report")
        .cronjob_uid("cron-abc-123")
        .job_name("daily-report-20231023")
        .job_uid("job-def-456")
        .pod_name("daily-report-20231023-pod-abc")
        .pod_uid("pod-ghi-789")
        .build()?;

    println!("  ✅ Created cronjob attributes:");
    for (key, value) in cronjob_attrs.to_attributes() {
        println!("     - {}: {}", key, value);
    }
    println!("\n============================================================\n");

    // Demo 8: Node Attributes
    println!("📊 Demo 8: Node Attributes");
    let node_attrs = K8sAttributesBuilder::new()
        .cluster_name("production")
        .node_name("worker-node-01")
        .node_uid("node-abc-123-def")
        .build()?;

    println!("  ✅ Created node attributes:");
    for (key, value) in node_attrs.to_attributes() {
        println!("     - {}: {}", key, value);
    }
    println!("\n============================================================\n");

    // Demo 9: Full Example - Complete Pod Information
    println!("📊 Demo 9: Complete Pod Information");
    let full_attrs = K8sAttributesBuilder::new()
        .cluster_name("production-us-east-1")
        .namespace_name("ecommerce")
        .deployment_name("checkout-service")
        .deployment_uid("deploy-abc-123")
        .replicaset_name("checkout-service-v2")
        .replicaset_uid("rs-def-456")
        .pod_name("checkout-service-v2-xyz789")
        .pod_uid("pod-ghi-789-jkl")
        .pod_label("app", "checkout")
        .pod_label("version", "v2")
        .pod_label("tier", "backend")
        .container_name("main")
        .container_id("containerd://abcdef123456")
        .container_image_name("myregistry.io/checkout-service")
        .container_image_tag("v2.1.0")
        .container_restart_count(0)
        .node_name("worker-node-us-east-1a-03")
        .node_uid("node-mno-123-pqr")
        .build()?;

    println!("  ✅ Created complete pod information:");
    let attributes_map = full_attrs.to_attributes();
    println!("     Total attributes: {}", attributes_map.len());
    for (key, value) in attributes_map {
        println!("     - {}: {}", key, value);
    }
    println!("\n============================================================\n");

    println!("✅ All Kubernetes semantic conventions demos completed successfully!\n");

    Ok(())
}
