//! Semantic Conventions Demonstration
//!
//! This example demonstrates all OpenTelemetry Semantic Conventions:
//! - HTTP (client/server)
//! - Database (PostgreSQL, Redis)
//! - FaaS (AWS Lambda)
//! - Cloud (AWS)
//! - Container (Kubernetes)
//! - Exception handling
//!
//! Run with: cargo run --example semantic_conventions_demo

use std::collections::HashMap;

use otlp::semantic_conventions::{
    // HTTP
    http::{HttpAttributesBuilder, HttpMethod, HttpScheme},
    
    // Database
    database::{
        DatabaseAttributesBuilder, DatabaseSystem, DatabaseOperation,
    },
    
    // FaaS
    faas::{
        FaasAttributesBuilder, FaasPlatform, FaasTriggerType,
        FaasInvocationResult, FaasDocumentOperation,
    },
    
    // Cloud
    cloud::{CloudAttributesBuilder, CloudProvider, CloudPlatform},
    
    // Container
    container::{
        ContainerAttributesBuilder, ContainerRuntime, ContainerState,
    },
    
    // Kubernetes
    k8s::{K8sAttributesBuilder, K8sResourceType},
    
    // Exception
    exception::{
        ExceptionAttributesBuilder, ErrorType, StackFrame,
    },
    
    // Common types
    common::{AttributeValue},
};

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    println!("╔══════════════════════════════════════════════════════════════╗");
    println!("║         Semantic Conventions Demonstration                   ║");
    println!("╚══════════════════════════════════════════════════════════════╝\n");

    // ====================================================================================
    // HTTP CONVENTIONS
    // ====================================================================================
    println!("📡 HTTP CONVENTIONS");
    println!("═════════════════════════════════════════════════════════════════\n");

    // HTTP Client Request
    println!("1️⃣  HTTP Client Request (Outgoing)");
    println!("─────────────────────────────────────────────────────────────────");
    let http_client_attrs = HttpAttributesBuilder::new()
        .method(HttpMethod::Post)
        .url("https://api.example.com/v1/users")
        .url_scheme(HttpScheme::Https)
        .url_path("/v1/users")
        .server_address("api.example.com")
        .server_port(443)
        .request_body_size(1024)
        .network_protocol_name("http")
        .network_protocol_version("2")
        .user_agent("MyApp/1.0")
        .custom_attribute("client.id", AttributeValue::String("mobile-app".to_string()))
        .build()?;

    print_attributes("HTTP Client", http_client_attrs.as_map());

    // HTTP Server Response
    println!("\n2️⃣  HTTP Server Response (Incoming)");
    println!("─────────────────────────────────────────────────────────────────");
    let http_server_attrs = HttpAttributesBuilder::new()
        .method(HttpMethod::Get)
        .url("https://api.example.com/v1/users/123")
        .status_code(200)
        .response_body_size(2048)
        .url_scheme(HttpScheme::Https)
        .server_address("api.example.com")
        .server_port(443)
        .network_protocol_name("http")
        .network_protocol_version("1.1")
        .user_agent("Mozilla/5.0 (compatible; Bot/1.0)")
        .custom_attribute("rate_limit.remaining", AttributeValue::Int(99))
        .build()?;

    print_attributes("HTTP Server", http_server_attrs.as_map());

    // Error Response
    println!("\n3️⃣  HTTP Error Response (500 Internal Server Error)");
    println!("─────────────────────────────────────────────────────────────────");
    let http_error_attrs = HttpAttributesBuilder::new()
        .method(HttpMethod::Put)
        .url("https://api.example.com/v1/users/123")
        .status_code(500)
        .request_body_size(512)
        .network_protocol_name("http")
        .network_protocol_version("1.1")
        .build()?;

    print_attributes("HTTP Error", http_error_attrs.as_map());

    // ====================================================================================
    // DATABASE CONVENTIONS
    // ====================================================================================
    println!("\n\n🗄️  DATABASE CONVENTIONS");
    println!("═════════════════════════════════════════════════════════════════\n");

    // PostgreSQL Query
    println!("1️⃣  PostgreSQL SELECT Query");
    println!("─────────────────────────────────────────────────────────────────");
    let postgres_attrs = DatabaseAttributesBuilder::new()
        .system(DatabaseSystem::Postgresql)
        .name("users_db")
        .statement("SELECT id, name, email FROM users WHERE active = $1")
        .operation(DatabaseOperation::Select)
        .sql_table("users")
        .user("app_readonly")
        .server_address("postgres.internal.example.com")
        .server_port(5432)
        .network_protocol_name("tcp")
        .build()?;

    print_db_attributes("PostgreSQL", &postgres_attrs);

    // Redis Cache Operation
    println!("\n2️⃣  Redis Cache GET Operation");
    println!("─────────────────────────────────────────────────────────────────");
    let redis_attrs = DatabaseAttributesBuilder::new()
        .system(DatabaseSystem::Redis)
        .name("session_cache")
        .statement("GET session:user:12345")
        .operation(DatabaseOperation::Get)
        .redis_database_index(0)
        .server_address("redis-cluster.example.com")
        .server_port(6379)
        .network_protocol_name("tcp")
        .build()?;

    print_db_attributes("Redis", &redis_attrs);

    // MongoDB Query
    println!("\n3️⃣  MongoDB findOne Operation");
    println!("─────────────────────────────────────────────────────────────────");
    let mongodb_attrs = DatabaseAttributesBuilder::new()
        .system(DatabaseSystem::Mongodb)
        .name("analytics_db")
        .statement(r#"{"_id": "user123", "active": true}"#)
        .operation(DatabaseOperation::Find)
        .mongodb_collection("user_events")
        .user("analytics_app")
        .server_address("mongodb.example.com")
        .server_port(27017)
        .build()?;

    print_db_attributes("MongoDB", &mongodb_attrs);

    // ====================================================================================
    // FaaS (Function-as-a-Service) CONVENTIONS
    // ====================================================================================
    println!("\n\n⚡ FaaS (Function-as-a-Service) CONVENTIONS");
    println!("═════════════════════════════════════════════════════════════════\n");

    // AWS Lambda HTTP Trigger
    println!("1️⃣  AWS Lambda - HTTP Trigger (API Gateway)");
    println!("─────────────────────────────────────────────────────────────────");
    let lambda_http_attrs = FaasAttributesBuilder::new()
        .platform(FaasPlatform::AwsLambda)
        .function_name("user-api-handler")
        .function_version("1.2.3")
        .max_memory(512)
        .timeout(30000)
        .cold_start(true)
        .request_id("c6af9ac6-7b61-11e6-9a41-93e8deadbeef")
        .trigger(FaasTriggerType::Http)
        .trigger_source("arn:aws:execute-api:us-east-1:123456789012:xyz123/prod/POST/users")
        .invocation_result(FaasInvocationResult::Success)
        .custom_attribute("aws.request_id", AttributeValue::String("c6af9ac6-7b61-11e6-9a41-93e8deadbeef".to_string()))
        .custom_attribute("lambda.runtime", AttributeValue::String("provided.al2".to_string()))
        .build()?;

    print_attributes("Lambda HTTP", lambda_http_attrs.as_map());

    // AWS Lambda Queue Trigger (SQS)
    println!("\n2️⃣  AWS Lambda - Queue Trigger (SQS)");
    println!("─────────────────────────────────────────────────────────────────");
    let lambda_queue_attrs = FaasAttributesBuilder::new()
        .platform(FaasPlatform::AwsLambda)
        .function_name("order-processor")
        .function_version("2.0.0")
        .cold_start(false)
        .request_id("a1b2c3d4-5678-90ab-cdef-example11111")
        .trigger(FaasTriggerType::Queue)
        .trigger_source("arn:aws:sqs:us-east-1:123456789012:order-queue")
        .message_id("msg-12345-abcde")
        .invocation_result(FaasInvocationResult::Success)
        .build()?;

    print_attributes("Lambda SQS", lambda_queue_attrs.as_map());

    // AWS Lambda Document Trigger (S3)
    println!("\n3️⃣  AWS Lambda - Document Trigger (S3 Object Create)");
    println!("─────────────────────────────────────────────────────────────────");
    let lambda_doc_attrs = FaasAttributesBuilder::new()
        .platform(FaasPlatform::AwsLambda)
        .function_name("image-resizer")
        .function_version("1.0.0")
        .cold_start(true)
        .trigger(FaasTriggerType::Event)
        .document_collection("uploads-bucket")
        .document_operation(FaasDocumentOperation::Insert)
        .document_name("user123/photo.jpg")
        .document_time("2024-01-15T10:30:00Z")
        .build()?;

    print_attributes("Lambda S3", lambda_doc_attrs.as_map());

    // Chained Lambda Invocation
    println!("\n4️⃣  AWS Lambda - Chained Invocation");
    println!("─────────────────────────────────────────────────────────────────");
    let lambda_chained_attrs = FaasAttributesBuilder::new()
        .platform(FaasPlatform::AwsLambda)
        .function_name("downstream-validator")
        .invoked_provider(FaasPlatform::AwsLambda)
        .invoked_region("us-west-2")
        .invoked_name("upstream-collector")
        .invocation_result(FaasInvocationResult::Success)
        .build()?;

    print_attributes("Lambda Chained", lambda_chained_attrs.as_map());

    // ====================================================================================
    // CLOUD CONVENTIONS
    // ====================================================================================
    println!("\n\n☁️  CLOUD CONVENTIONS");
    println!("═════════════════════════════════════════════════════════════════\n");

    // AWS EC2 Instance
    println!("1️⃣  AWS EC2 Instance");
    println!("─────────────────────────────────────────────────────────────────");
    let aws_ec2_attrs = CloudAttributesBuilder::new()
        .platform(CloudPlatform::AwsEc2)
        .region("us-east-1")
        .availability_zone("us-east-1a")
        .account_id("123456789012")
        .instance_id("i-0abcd1234efgh5678")
        .instance_type("t3.medium")
        .image_id("ami-0c55b159cbfafe1f0")
        .resource_id("arn:aws:ec2:us-east-1:123456789012:instance/i-0abcd1234efgh5678")
        .custom_attribute("aws.vpc.id", AttributeValue::String("vpc-12345abc".to_string()))
        .custom_attribute("aws.subnet.id", AttributeValue::String("subnet-67890def".to_string()))
        .build()?;

    print_attributes("AWS EC2", aws_ec2_attrs.as_map());

    // AWS Lambda Environment
    println!("\n2️⃣  AWS Lambda Environment");
    println!("─────────────────────────────────────────────────────────────────");
    let aws_lambda_cloud_attrs = CloudAttributesBuilder::new()
        .platform(CloudPlatform::AwsLambda)
        .region("us-west-2")
        .account_id("123456789012")
        .resource_id("arn:aws:lambda:us-west-2:123456789012:function:my-function")
        .build()?;

    print_attributes("AWS Lambda Cloud", aws_lambda_cloud_attrs.as_map());

    // GCP Cloud Run
    println!("\n3️⃣  GCP Cloud Run Service");
    println!("─────────────────────────────────────────────────────────────────");
    let gcp_cloud_run_attrs = CloudAttributesBuilder::new()
        .platform(CloudPlatform::GcpCloudRun)
        .region("us-central1")
        .project_id("my-gcp-project-123456")
        .resource_id("projects/my-gcp-project-123456/locations/us-central1/services/my-service")
        .custom_attribute("gcp.cloud_run.revision", AttributeValue::String("my-service-00001-abcd".to_string()))
        .build()?;

    print_attributes("GCP Cloud Run", gcp_cloud_run_attrs.as_map());

    // Azure Kubernetes Service
    println!("\n4️⃣  Azure Kubernetes Service (AKS)");
    println!("─────────────────────────────────────────────────────────────────");
    let azure_aks_attrs = CloudAttributesBuilder::new()
        .platform(CloudPlatform::AzureAks)
        .region("westeurope")
        .account_id("12345678-1234-1234-1234-123456789012")
        .resource_id("/subscriptions/12345678-1234-1234-1234-123456789012/resourceGroups/my-rg/providers/Microsoft.ContainerService/managedClusters/my-aks")
        .custom_attribute("azure.node_pool", AttributeValue::String("system".to_string()))
        .build()?;

    print_attributes("Azure AKS", azure_aks_attrs.as_map());

    // ====================================================================================
    // CONTAINER CONVENTIONS
    // ====================================================================================
    println!("\n\n🐳 CONTAINER CONVENTIONS");
    println!("═════════════════════════════════════════════════════════════════\n");

    // Docker Container
    println!("1️⃣  Docker Container (Running)");
    println!("─────────────────────────────────────────────────────────────────");
    let docker_attrs = ContainerAttributesBuilder::new()
        .runtime(ContainerRuntime::Docker)
        .name("user-service")
        .id("abc123def456789")
        .image_name("myregistry/user-service")
        .image_tag("v1.2.3")
        .state(ContainerState::Running)
        .command(vec!["/app/server".to_string()])
        .custom_attribute("docker.network", AttributeValue::String("bridge".to_string()))
        .custom_attribute("docker.restart_count", AttributeValue::Int(0))
        .build()?;

    print_attributes("Docker", docker_attrs.as_map());

    // Containerd Container
    println!("\n2️⃣  Containerd Container (Paused)");
    println!("─────────────────────────────────────────────────────────────────");
    let containerd_attrs = ContainerAttributesBuilder::new()
        .runtime(ContainerRuntime::Containerd)
        .name("api-gateway")
        .id("containerd://xyz789abc")
        .image_name("gcr.io/project/api-gateway")
        .image_tag("latest")
        .state(ContainerState::Paused)
        .custom_attribute("containerd.namespace", AttributeValue::String("k8s.io".to_string()))
        .build()?;

    print_attributes("Containerd", containerd_attrs.as_map());

    // ====================================================================================
    // KUBERNETES CONVENTIONS
    // ====================================================================================
    println!("\n\n☸️  KUBERNETES CONVENTIONS");
    println!("═════════════════════════════════════════════════════════════════\n");

    // Kubernetes Pod
    println!("1️⃣  Kubernetes Pod");
    println!("─────────────────────────────────────────────────────────────────");
    let k8s_pod_attrs = K8sAttributesBuilder::new()
        .resource_type(K8sResourceType::Pod)
        .pod_name("user-service-7d8f9b2c4-a1b2c")
        .pod_uid("a1b2c3d4-e5f6-7890-abcd-ef1234567890")
        .namespace_name("production")
        .node_name("ip-10-0-1-123.us-east-1.compute.internal")
        .deployment_name("user-service")
        .replicaset_name("user-service-7d8f9b2c4")
        .container_name("user-service")
        .cluster_name("production-eks")
        .custom_attribute("app.version", AttributeValue::String("1.2.3".to_string()))
        .custom_attribute("app.component", AttributeValue::String("backend".to_string()))
        .build()?;

    print_attributes("K8s Pod", k8s_pod_attrs.as_map());

    // Kubernetes Service
    println!("\n2️⃣  Kubernetes Service");
    println!("─────────────────────────────────────────────────────────────────");
    let k8s_service_attrs = K8sAttributesBuilder::new()
        .resource_type(K8sResourceType::Service)
        .service_name("user-service")
        .namespace_name("production")
        .cluster_name("production-eks")
        .custom_attribute("service.type", AttributeValue::String("ClusterIP".to_string()))
        .custom_attribute("service.port", AttributeValue::Int(8080))
        .build()?;

    print_attributes("K8s Service", k8s_service_attrs.as_map());

    // Kubernetes Deployment
    println!("\n3️⃣  Kubernetes Deployment");
    println!("─────────────────────────────────────────────────────────────────");
    let k8s_deployment_attrs = K8sAttributesBuilder::new()
        .resource_type(K8sResourceType::Deployment)
        .deployment_name("user-service")
        .namespace_name("production")
        .cluster_name("production-eks")
        .replicaset_name("user-service-7d8f9b2c4")
        .custom_attribute("deployment.replicas", AttributeValue::Int(3))
        .custom_attribute("deployment.strategy", AttributeValue::String("RollingUpdate".to_string()))
        .build()?;

    print_attributes("K8s Deployment", k8s_deployment_attrs.as_map());

    // ====================================================================================
    // EXCEPTION CONVENTIONS
    // ====================================================================================
    println!("\n\n⚠️  EXCEPTION CONVENTIONS");
    println!("═════════════════════════════════════════════════════════════════\n");

    // Database Connection Error
    println!("1️⃣  Database Connection Exception");
    println!("─────────────────────────────────────────────────────────────────");
    let db_exception_attrs = ExceptionAttributesBuilder::new()
        .exception_type("DatabaseConnectionError")
        .message("Failed to connect to PostgreSQL: connection refused")
        .stack_trace("DatabaseConnectionError: connection refused
  at /app/src/db.rs:42:10
  at /app/src/main.rs:25:5")
        .escaped(true)
        .error_type(ErrorType::Database)
        .error_code("ECONNREFUSED")
        .target("postgresql://localhost:5432/mydb")
        .custom_attribute("db.retry_count", AttributeValue::Int(3))
        .custom_attribute("db.retryable", AttributeValue::Bool(true))
        .build()?;

    print_attributes("DB Exception", db_exception_attrs.as_map());

    // Network Timeout Error
    println!("\n2️⃣  Network Timeout Exception");
    println!("─────────────────────────────────────────────────────────────────");
    let network_exception_attrs = ExceptionAttributesBuilder::new()
        .exception_type("RequestTimeoutError")
        .message("Request to external API timed out after 30s")
        .error_type(ErrorType::Timeout)
        .error_code("ETIMEDOUT")
        .target("https://api.external.com/v1/data")
        .custom_attribute("http.timeout_ms", AttributeValue::Int(30000))
        .custom_attribute("http.attempt", AttributeValue::Int(2))
        .build()?;

    print_attributes("Network Exception", network_exception_attrs.as_map());

    // Structured Stack Trace
    println!("\n3️⃣  Exception with Structured Stack Frames");
    println!("─────────────────────────────────────────────────────────────────");
    let frames = vec![
        StackFrame::new("process_order")
            .with_file("/app/src/orders/handlers.rs")
            .with_line(45)
            .with_column(12)
            .with_module("orders::handlers"),
        StackFrame::new("validate_payment")
            .with_file("/app/src/payments/validation.rs")
            .with_line(88)
            .with_column(5)
            .with_module("payments::validation"),
        StackFrame::new("check_funds")
            .with_file("/app/src/payments/balance.rs")
            .with_line(23)
            .with_module("payments::balance"),
    ];

    let structured_exception_attrs = ExceptionAttributesBuilder::new()
        .exception_type("PaymentValidationError")
        .message("Insufficient funds for transaction")
        .stack_frames(frames)
        .escaped(false)
        .error_type(ErrorType::Validation)
        .error_code("INSUFFICIENT_FUNDS")
        .target("payment-gateway")
        .custom_attribute("transaction.id", AttributeValue::String("txn-abc-123".to_string()))
        .custom_attribute("transaction.amount", AttributeValue::Double(150.00))
        .build()?;

    print_attributes("Structured Exception", structured_exception_attrs.as_map());

    // Authentication Error
    println!("\n4️⃣  Authentication Exception");
    println!("─────────────────────────────────────────────────────────────────");
    let auth_exception_attrs = ExceptionAttributesBuilder::new()
        .exception_type("AuthenticationFailedError")
        .message("Invalid JWT token: token expired")
        .escaped(true)
        .error_type(ErrorType::Auth)
        .error_code("TOKEN_EXPIRED")
        .target("auth-service")
        .custom_attribute("auth.token_issued_at", AttributeValue::String("2024-01-10T10:00:00Z".to_string()))
        .custom_attribute("auth.token_expires_at", AttributeValue::String("2024-01-10T11:00:00Z".to_string()))
        .build()?;

    print_attributes("Auth Exception", auth_exception_attrs.as_map());

    // ====================================================================================
    // Summary
    // ====================================================================================
    println!("\n╔══════════════════════════════════════════════════════════════╗");
    println!("║                    Conventions Summary                       ║");
    println!("╠══════════════════════════════════════════════════════════════╣");
    println!("║                                                              ║");
    println!("║  ✅ HTTP Conventions         - Client/Server attributes      ║");
    println!("║  ✅ Database Conventions     - PostgreSQL, Redis, MongoDB    ║");
    println!("║  ✅ FaaS Conventions         - AWS Lambda triggers           ║");
    println!("║  ✅ Cloud Conventions        - AWS, GCP, Azure               ║");
    println!("║  ✅ Container Conventions    - Docker, Containerd            ║");
    println!("║  ✅ Kubernetes Conventions   - Pods, Services, Deployments   ║");
    println!("║  ✅ Exception Conventions    - Errors with stack traces      ║");
    println!("║                                                              ║");
    println!("╚══════════════════════════════════════════════════════════════╝");
    
    println!("\n📚 Reference: https://opentelemetry.io/docs/specs/semconv/");

    Ok(())
}

/// Helper function to print attributes
fn print_attributes(label: &str, attrs: &HashMap<String, AttributeValue>) {
    println!("   Attributes:");
    for (key, value) in attrs {
        println!("      • {} = {}", key, format_value(value));
    }
    if attrs.is_empty() {
        println!("      (none)");
    }
}

/// Helper function to print database attributes
fn print_db_attributes(label: &str, attrs: &otlp::semantic_conventions::database::DatabaseAttributes) {
    let map = attrs.to_attributes();
    print_attributes(label, &map);
}

/// Helper function to format attribute values
fn format_value(value: &AttributeValue) -> String {
    match value {
        AttributeValue::String(s) => format!("\"{}\"", s),
        AttributeValue::Int(i) => i.to_string(),
        AttributeValue::Double(d) => format!("{:.2}", d),
        AttributeValue::Bool(b) => b.to_string(),
        AttributeValue::Array(arr) => format!("[{} items]", arr.len()),
        AttributeValue::Map(m) => format!("{{{} entries}}", m.len()),
    }
}
