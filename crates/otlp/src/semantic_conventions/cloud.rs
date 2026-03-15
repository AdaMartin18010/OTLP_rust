//! # Cloud Provider Semantic Conventions
//!
//! Implementation of OpenTelemetry Cloud Semantic Conventions v1.38.0
//! <https://opentelemetry.io/docs/specs/semconv/resource/cloud/>
//!
//! ## Supported Providers
//!
//! - **AWS**: Amazon Web Services
//! - **Azure**: Microsoft Azure
//! - **GCP**: Google Cloud Platform
//! - **Alibaba Cloud**: Alibaba Cloud
//! - **Tencent Cloud**: Tencent Cloud
//! - **IBM Cloud**: IBM Cloud
//! - **Oracle Cloud**: Oracle Cloud Infrastructure
//! - **Heroku**: Salesforce Heroku
//!
//! ## Rust 1.92 Features
//!
//! - **Type-safe providers**: Enum-based cloud provider definitions
//! - **Builder pattern**: Ergonomic cloud attribute construction
//! - **Cross-cloud abstractions**: Generic cloud attributes across providers
//!
//! ## Usage Example
//!
//! ```rust
//! use otlp::semantic_conventions::cloud::{
//!     CloudAttributesBuilder, CloudProvider, CloudPlatform,
//! };
//!
//! let attrs = CloudAttributesBuilder::new()
//!     .provider(CloudProvider::Aws)
//!     .platform(CloudPlatform::AwsLambda)
//!     .region("us-east-1")
//!     .account_id("123456789012")
//!     .build()
//!     .unwrap();
//! ```

use super::common::{AttributeMap, AttributeValue, Result, SemanticConventionError};
use std::collections::HashMap;

/// Cloud providers
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CloudProvider {
    /// Amazon Web Services
    Aws,
    /// Microsoft Azure
    Azure,
    /// Google Cloud Platform
    Gcp,
    /// Alibaba Cloud
    AlibabaCloud,
    /// Tencent Cloud
    TencentCloud,
    /// IBM Cloud
    IbmCloud,
    /// Oracle Cloud Infrastructure
    Oci,
    /// Heroku
    Heroku,
    /// Other provider
    Other,
}

impl CloudProvider {
    /// Returns the string representation
    pub fn as_str(&self) -> &'static str {
        match self {
            CloudProvider::Aws => "aws",
            CloudProvider::Azure => "azure",
            CloudProvider::Gcp => "gcp",
            CloudProvider::AlibabaCloud => "alibaba_cloud",
            CloudProvider::TencentCloud => "tencent_cloud",
            CloudProvider::IbmCloud => "ibm_cloud",
            CloudProvider::Oci => "oci",
            CloudProvider::Heroku => "heroku",
            CloudProvider::Other => "other",
        }
    }
}

impl std::fmt::Display for CloudProvider {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.as_str())
    }
}

/// Cloud platforms/services
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CloudPlatform {
    // AWS Platforms
    /// AWS Lambda
    AwsLambda,
    /// AWS Elastic Beanstalk
    AwsElasticBeanstalk,
    /// AWS ECS (Elastic Container Service)
    AwsEcs,
    /// AWS EKS (Elastic Kubernetes Service)
    AwsEks,
    /// AWS EC2 (Elastic Compute Cloud)
    AwsEc2,
    /// AWS Fargate
    AwsFargate,
    /// AWS SageMaker
    AwsSagemaker,
    /// AWS App Runner
    AwsAppRunner,

    // Azure Platforms
    /// Azure Virtual Machines
    AzureVm,
    /// Azure Container Apps
    AzureContainerApps,
    /// Azure Container Instances
    AzureContainerInstances,
    /// Azure AKS (Azure Kubernetes Service)
    AzureAks,
    /// Azure Functions
    AzureFunctions,
    /// Azure App Service
    AzureAppService,
    /// Azure Spring Apps
    AzureSpringApps,

    // GCP Platforms
    /// GCP Compute Engine
    GcpComputeEngine,
    /// GCP Cloud Run
    GcpCloudRun,
    /// GCP Cloud Functions
    GcpCloudFunctions,
    /// GCP Cloud Apps
    GcpAppEngine,
    /// GCP GKE (Google Kubernetes Engine)
    GcpGke,
    /// GCP Cloud Batch
    GcpCloudBatch,

    // Alibaba Cloud Platforms
    /// Alibaba Cloud ECS
    AlibabaCloudEcs,
    /// Alibaba Cloud Function Compute
    AlibabaCloudFc,
    /// Alibaba Cloud K8s
    AlibabaCloudAck,

    // Tencent Cloud Platforms
    /// Tencent Cloud CVM
    TencentCloudCvm,
    /// Tencent Cloud SCF
    TencentCloudScf,
    /// Tencent Cloud TKE
    TencentCloudTke,

    // Other
    /// Other platform
    Other,
}

impl CloudPlatform {
    /// Returns the string representation
    pub fn as_str(&self) -> &'static str {
        match self {
            // AWS
            CloudPlatform::AwsLambda => "aws_lambda",
            CloudPlatform::AwsElasticBeanstalk => "aws_elastic_beanstalk",
            CloudPlatform::AwsEcs => "aws_ecs",
            CloudPlatform::AwsEks => "aws_eks",
            CloudPlatform::AwsEc2 => "aws_ec2",
            CloudPlatform::AwsFargate => "aws_fargate",
            CloudPlatform::AwsSagemaker => "aws_sagemaker",
            CloudPlatform::AwsAppRunner => "aws_app_runner",

            // Azure
            CloudPlatform::AzureVm => "azure_vm",
            CloudPlatform::AzureContainerApps => "azure_container_apps",
            CloudPlatform::AzureContainerInstances => "azure_container_instances",
            CloudPlatform::AzureAks => "azure_aks",
            CloudPlatform::AzureFunctions => "azure_functions",
            CloudPlatform::AzureAppService => "azure_app_service",
            CloudPlatform::AzureSpringApps => "azure_spring_apps",

            // GCP
            CloudPlatform::GcpComputeEngine => "gcp_compute_engine",
            CloudPlatform::GcpCloudRun => "gcp_cloud_run",
            CloudPlatform::GcpCloudFunctions => "gcp_cloud_functions",
            CloudPlatform::GcpAppEngine => "gcp_app_engine",
            CloudPlatform::GcpGke => "gcp_kubernetes_engine",
            CloudPlatform::GcpCloudBatch => "gcp_cloud_batch",

            // Alibaba Cloud
            CloudPlatform::AlibabaCloudEcs => "alibaba_cloud_ecs",
            CloudPlatform::AlibabaCloudFc => "alibaba_cloud_fc",
            CloudPlatform::AlibabaCloudAck => "alibaba_cloud_ack",

            // Tencent Cloud
            CloudPlatform::TencentCloudCvm => "tencent_cloud_cvm",
            CloudPlatform::TencentCloudScf => "tencent_cloud_scf",
            CloudPlatform::TencentCloudTke => "tencent_cloud_tke",

            // Other
            CloudPlatform::Other => "other",
        }
    }

    /// Returns the associated CloudProvider for this platform
    pub fn provider(&self) -> CloudProvider {
        match self {
            CloudPlatform::AwsLambda
            | CloudPlatform::AwsElasticBeanstalk
            | CloudPlatform::AwsEcs
            | CloudPlatform::AwsEks
            | CloudPlatform::AwsEc2
            | CloudPlatform::AwsFargate
            | CloudPlatform::AwsSagemaker
            | CloudPlatform::AwsAppRunner => CloudProvider::Aws,

            CloudPlatform::AzureVm
            | CloudPlatform::AzureContainerApps
            | CloudPlatform::AzureContainerInstances
            | CloudPlatform::AzureAks
            | CloudPlatform::AzureFunctions
            | CloudPlatform::AzureAppService
            | CloudPlatform::AzureSpringApps => CloudProvider::Azure,

            CloudPlatform::GcpComputeEngine
            | CloudPlatform::GcpCloudRun
            | CloudPlatform::GcpCloudFunctions
            | CloudPlatform::GcpAppEngine
            | CloudPlatform::GcpGke
            | CloudPlatform::GcpCloudBatch => CloudProvider::Gcp,

            CloudPlatform::AlibabaCloudEcs
            | CloudPlatform::AlibabaCloudFc
            | CloudPlatform::AlibabaCloudAck => CloudProvider::AlibabaCloud,

            CloudPlatform::TencentCloudCvm
            | CloudPlatform::TencentCloudScf
            | CloudPlatform::TencentCloudTke => CloudProvider::TencentCloud,

            CloudPlatform::Other => CloudProvider::Other,
        }
    }
}

impl std::fmt::Display for CloudPlatform {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.as_str())
    }
}

/// Cloud attributes following OpenTelemetry semantic conventions
#[derive(Debug, Clone)]
pub struct CloudAttributes {
    attributes: AttributeMap,
}

impl CloudAttributes {
    /// Get all attributes as a map
    pub fn as_map(&self) -> &AttributeMap {
        &self.attributes
    }

    /// Get a specific attribute
    pub fn get(&self, key: &str) -> Option<&AttributeValue> {
        self.attributes.get(key)
    }
}

/// Builder for cloud attributes
#[derive(Debug, Default)]
pub struct CloudAttributesBuilder {
    // Required
    provider: Option<CloudProvider>,

    // Account/Project
    account_id: Option<String>,
    project_id: Option<String>,

    // Location
    region: Option<String>,
    availability_zone: Option<String>,

    // Platform
    platform: Option<CloudPlatform>,

    // VM/Instance attributes
    instance_id: Option<String>,
    instance_type: Option<String>,
    image_id: Option<String>,

    // Resource attributes
    resource_id: Option<String>,

    // Custom attributes
    custom: HashMap<String, AttributeValue>,
}

impl CloudAttributesBuilder {
    /// Create a new builder
    pub fn new() -> Self {
        Self::default()
    }

    /// Set cloud provider (required)
    pub fn provider(mut self, provider: CloudProvider) -> Self {
        self.provider = Some(provider);
        self
    }

    /// Set cloud platform/service
    pub fn platform(mut self, platform: CloudPlatform) -> Self {
        self.platform = Some(platform);
        // Auto-set provider if platform is known
        self.provider = Some(platform.provider());
        self
    }

    /// Set account ID (AWS Account ID, Azure Subscription ID, etc.)
    pub fn account_id(mut self, id: impl Into<String>) -> Self {
        self.account_id = Some(id.into());
        self
    }

    /// Set project ID (GCP Project ID)
    pub fn project_id(mut self, id: impl Into<String>) -> Self {
        self.project_id = Some(id.into());
        self
    }

    /// Set region
    pub fn region(mut self, region: impl Into<String>) -> Self {
        self.region = Some(region.into());
        self
    }

    /// Set availability zone
    pub fn availability_zone(mut self, zone: impl Into<String>) -> Self {
        self.availability_zone = Some(zone.into());
        self
    }

    /// Set VM instance ID
    pub fn instance_id(mut self, id: impl Into<String>) -> Self {
        self.instance_id = Some(id.into());
        self
    }

    /// Set instance type (e.g., "t2.micro", "Standard_D2s_v3")
    pub fn instance_type(mut self, instance_type: impl Into<String>) -> Self {
        self.instance_type = Some(instance_type.into());
        self
    }

    /// Set image ID
    pub fn image_id(mut self, id: impl Into<String>) -> Self {
        self.image_id = Some(id.into());
        self
    }

    /// Set cloud resource ID
    pub fn resource_id(mut self, id: impl Into<String>) -> Self {
        self.resource_id = Some(id.into());
        self
    }

    /// Add a custom attribute
    pub fn custom_attribute(mut self, key: impl Into<String>, value: AttributeValue) -> Self {
        self.custom.insert(key.into(), value);
        self
    }

    /// Build the cloud attributes
    pub fn build(self) -> Result<CloudAttributes> {
        let provider = self.provider.ok_or_else(|| {
            SemanticConventionError::MissingRequired("cloud.provider".to_string())
        })?;

        let mut attributes = AttributeMap::new();

        // Required
        attributes.insert(
            "cloud.provider".to_string(),
            AttributeValue::String(provider.as_str().to_string()),
        );

        // Optional
        if let Some(platform) = self.platform {
            attributes.insert(
                "cloud.platform".to_string(),
                AttributeValue::String(platform.as_str().to_string()),
            );
        }

        if let Some(id) = self.account_id {
            attributes.insert(
                "cloud.account.id".to_string(),
                AttributeValue::String(id),
            );
        }

        if let Some(id) = self.project_id {
            // In OTel, GCP project ID maps to cloud.account.id
            // but we also store it separately for clarity
            attributes.insert(
                "cloud.account.id".to_string(),
                AttributeValue::String(id.clone()),
            );
            attributes.insert(
                "gcp.project.id".to_string(),
                AttributeValue::String(id),
            );
        }

        if let Some(region) = self.region {
            attributes.insert(
                "cloud.region".to_string(),
                AttributeValue::String(region),
            );
        }

        if let Some(zone) = self.availability_zone {
            attributes.insert(
                "cloud.availability_zone".to_string(),
                AttributeValue::String(zone),
            );
        }

        if let Some(id) = self.instance_id {
            attributes.insert(
                "host.id".to_string(),
                AttributeValue::String(id),
            );
        }

        if let Some(instance_type) = self.instance_type {
            attributes.insert(
                "host.type".to_string(),
                AttributeValue::String(instance_type),
            );
        }

        if let Some(id) = self.image_id {
            attributes.insert(
                "host.image.id".to_string(),
                AttributeValue::String(id),
            );
        }

        if let Some(id) = self.resource_id {
            attributes.insert(
                "cloud.resource_id".to_string(),
                AttributeValue::String(id),
            );
        }

        // Add custom attributes
        attributes.extend(self.custom);

        Ok(CloudAttributes { attributes })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_cloud_provider() {
        assert_eq!(CloudProvider::Aws.as_str(), "aws");
        assert_eq!(CloudProvider::Azure.as_str(), "azure");
        assert_eq!(CloudProvider::Gcp.as_str(), "gcp");
        assert_eq!(CloudProvider::AlibabaCloud.as_str(), "alibaba_cloud");
    }

    #[test]
    fn test_cloud_platform() {
        assert_eq!(CloudPlatform::AwsLambda.as_str(), "aws_lambda");
        assert_eq!(CloudPlatform::AzureFunctions.as_str(), "azure_functions");
        assert_eq!(CloudPlatform::GcpCloudRun.as_str(), "gcp_cloud_run");
    }

    #[test]
    fn test_cloud_platform_provider() {
        assert_eq!(CloudPlatform::AwsLambda.provider(), CloudProvider::Aws);
        assert_eq!(CloudPlatform::AzureVm.provider(), CloudProvider::Azure);
        assert_eq!(CloudPlatform::GcpGke.provider(), CloudProvider::Gcp);
    }

    #[test]
    fn test_cloud_attributes_builder_minimal() {
        let attrs = CloudAttributesBuilder::new()
            .provider(CloudProvider::Aws)
            .build()
            .unwrap();

        assert_eq!(
            attrs.get("cloud.provider"),
            Some(&AttributeValue::String("aws".to_string()))
        );
    }

    #[test]
    fn test_cloud_attributes_builder_full() {
        let attrs = CloudAttributesBuilder::new()
            .provider(CloudProvider::Aws)
            .platform(CloudPlatform::AwsEc2)
            .region("us-east-1")
            .availability_zone("us-east-1a")
            .account_id("123456789012")
            .instance_id("i-abc123def456")
            .instance_type("t2.micro")
            .image_id("ami-12345678")
            .build()
            .unwrap();

        assert_eq!(
            attrs.get("cloud.platform"),
            Some(&AttributeValue::String("aws_ec2".to_string()))
        );
        assert_eq!(
            attrs.get("cloud.region"),
            Some(&AttributeValue::String("us-east-1".to_string()))
        );
        assert_eq!(
            attrs.get("cloud.availability_zone"),
            Some(&AttributeValue::String("us-east-1a".to_string()))
        );
        assert_eq!(
            attrs.get("cloud.account.id"),
            Some(&AttributeValue::String("123456789012".to_string()))
        );
        assert_eq!(
            attrs.get("host.id"),
            Some(&AttributeValue::String("i-abc123def456".to_string()))
        );
        assert_eq!(
            attrs.get("host.type"),
            Some(&AttributeValue::String("t2.micro".to_string()))
        );
    }

    #[test]
    fn test_cloud_platform_auto_sets_provider() {
        let attrs = CloudAttributesBuilder::new()
            .platform(CloudPlatform::GcpCloudFunctions)
            .region("us-central1")
            .build()
            .unwrap();

        assert_eq!(
            attrs.get("cloud.provider"),
            Some(&AttributeValue::String("gcp".to_string()))
        );
        assert_eq!(
            attrs.get("cloud.platform"),
            Some(&AttributeValue::String("gcp_cloud_functions".to_string()))
        );
    }

    #[test]
    fn test_gcp_project_id() {
        let attrs = CloudAttributesBuilder::new()
            .provider(CloudProvider::Gcp)
            .project_id("my-gcp-project")
            .region("europe-west1")
            .build()
            .unwrap();

        assert_eq!(
            attrs.get("cloud.account.id"),
            Some(&AttributeValue::String("my-gcp-project".to_string()))
        );
        assert_eq!(
            attrs.get("gcp.project.id"),
            Some(&AttributeValue::String("my-gcp-project".to_string()))
        );
    }

    #[test]
    fn test_azure_attributes() {
        let attrs = CloudAttributesBuilder::new()
            .provider(CloudProvider::Azure)
            .platform(CloudPlatform::AzureAks)
            .region("westeurope")
            .account_id("12345678-1234-1234-1234-123456789012")
            .build()
            .unwrap();

        assert_eq!(
            attrs.get("cloud.provider"),
            Some(&AttributeValue::String("azure".to_string()))
        );
        assert_eq!(
            attrs.get("cloud.platform"),
            Some(&AttributeValue::String("azure_aks".to_string()))
        );
    }

    #[test]
    fn test_cloud_attributes_builder_missing_required() {
        let result = CloudAttributesBuilder::new().build();

        assert!(result.is_err());
        match result {
            Err(SemanticConventionError::MissingRequired(field)) => {
                assert_eq!(field, "cloud.provider");
            }
            _ => panic!("Expected MissingRequired error"),
        }
    }

    #[test]
    fn test_cloud_custom_attributes() {
        let attrs = CloudAttributesBuilder::new()
            .provider(CloudProvider::Aws)
            .custom_attribute("custom.vpc_id", AttributeValue::String("vpc-123".to_string()))
            .custom_attribute("custom.subnet_id", AttributeValue::String("subnet-456".to_string()))
            .build()
            .unwrap();

        assert_eq!(
            attrs.get("custom.vpc_id"),
            Some(&AttributeValue::String("vpc-123".to_string()))
        );
        assert_eq!(
            attrs.get("custom.subnet_id"),
            Some(&AttributeValue::String("subnet-456".to_string()))
        );
    }

    #[test]
    fn test_all_platforms() {
        let platforms = vec![
            CloudPlatform::AwsLambda,
            CloudPlatform::AwsEcs,
            CloudPlatform::AwsEks,
            CloudPlatform::AwsEc2,
            CloudPlatform::AzureFunctions,
            CloudPlatform::AzureAks,
            CloudPlatform::GcpCloudRun,
            CloudPlatform::GcpGke,
        ];

        for platform in platforms {
            let attrs = CloudAttributesBuilder::new()
                .platform(platform)
                .build()
                .unwrap();

            assert!(
                attrs.get("cloud.platform").is_some(),
                "cloud.platform should be present"
            );
            assert!(
                attrs.get("cloud.provider").is_some(),
                "cloud.provider should be present"
            );
        }
    }
}
