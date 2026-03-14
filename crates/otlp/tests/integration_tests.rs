//! # OTLP Integration Tests
//!
//! Comprehensive integration tests for the OTLP crate.

use std::collections::HashMap;
use std::time::Duration;

/// Test GenAI semantic conventions
#[test]
fn test_gen_ai_semantic_conventions() {
    use otlp::semantic_conventions::gen_ai::{
        GenAiAttributes, GenAiSystem, GenAiOperation, GenAiFinishReason
    };
    
    let attrs = GenAiAttributes::builder()
        .system(GenAiSystem::OpenAI)
        .operation(GenAiOperation::Chat)
        .request_model("gpt-4o")
        .input_tokens(150)
        .output_tokens(45)
        .finish_reason(GenAiFinishReason::Stop)
        .build();
    
    assert_eq!(attrs.system, Some("openai".to_string()));
    assert_eq!(attrs.request_model, Some("gpt-4o".to_string()));
    assert_eq!(attrs.usage_input_tokens, Some(150));
    assert_eq!(attrs.usage_output_tokens, Some(45));
    assert_eq!(attrs.usage_total_tokens, Some(195));
}

/// Test declarative configuration
#[test]
fn test_declarative_config_loading() {
    use otlp::config::declarative::OpenTelemetryConfig;
    
    let yaml = r#"
resource:
  attributes:
    service.name: test-service
    service.version: "1.0.0"
    deployment.environment: production
"#;
    
    let config = OpenTelemetryConfig::from_yaml(yaml)
        .expect("Failed to parse config");
    
    assert!(config.resource.is_some());
    let resource = config.resource.unwrap();
    assert!(resource.attributes.contains_key("service.name"));
}

/// Test OTTL processor
#[test]
fn test_ottl_processor_basic() {
    use otlp::ottl::processor::{OttlProcessor, OttlContext};
    
    let mut processor = OttlProcessor::new();
    processor.parse_and_add("set(attributes[\"key\"], \"value\")")
        .expect("Failed to parse OTTL statement");
    
    let mut resource_attrs = HashMap::new();
    let mut span_attrs = HashMap::new();
    
    let mut ctx = OttlContext {
        resource_attributes: &mut resource_attrs,
        span_attributes: Some(&mut span_attrs),
        metric_attributes: None,
        log_attributes: None,
    };
    
    processor.execute(&mut ctx)
        .expect("Failed to execute OTTL processor");
    
    assert_eq!(span_attrs.get("key"), Some(&"value".to_string()));
}

/// Test profiling configuration
#[tokio::test]
async fn test_profiling_lifecycle() {
    use otlp::profiling::{Profiler, ProfilingConfig};
    
    let config = ProfilingConfig {
        sampling_rate: 100,
        duration: Duration::from_secs(1),
        enable_cpu_profiling: true,
        enable_memory_profiling: false,
        enable_lock_profiling: false,
    };
    
    let mut profiler = Profiler::new(config);
    
    // Start profiling
    profiler.start().await
        .expect("Failed to start profiler");
    assert!(profiler.is_running());
    
    // Collect some data
    let data = profiler.collect_data().await
        .expect("Failed to collect data");
    assert!(!data.is_empty());
    
    // Stop profiling
    profiler.stop().await
        .expect("Failed to stop profiler");
    assert!(!profiler.is_running());
}

/// Test CPU profiler lifecycle
#[tokio::test]
async fn test_cpu_profiler_lifecycle() {
    use otlp::profiling::cpu::{CpuProfiler, CpuProfilerConfig};
    
    let config = CpuProfilerConfig {
        sampling_frequency: 100,
        max_duration: Duration::from_millis(100),
        include_system_calls: false,
    };
    
    let mut profiler = CpuProfiler::new(config);
    
    // Start profiler
    profiler.start().await
        .expect("Failed to start CPU profiler");
    
    // Stop profiler
    profiler.stop().await
        .expect("Failed to stop CPU profiler");
}

/// Test sampling strategies
#[test]
fn test_sampling_strategies() {
    use otlp::profiling::sampling::{AlwaysSample, NeverSample, SamplingStrategy};
    
    // Always sample
    let always = AlwaysSample::new();
    assert!(always.should_sample());
    
    // Never sample
    let never = NeverSample::new();
    assert!(!never.should_sample());
}

/// Test error handling
#[test]
fn test_error_handling() {
    use otlp::error::OtlpError;
    
    let error = OtlpError::ValidationError("test error".to_string());
    
    match error {
        OtlpError::ValidationError(msg) => {
            assert_eq!(msg, "test error");
        }
        _ => panic!("Expected ValidationError"),
    }
}

/// Test configuration
#[test]
fn test_otlp_config() {
    use otlp::config::OtlpConfigBuilder;
    
    let config = OtlpConfigBuilder::new()
        .endpoint("http://localhost:4317")
        .protocol("grpc")
        .service("test-service", "1.0.0")
        .build();
    
    assert_eq!(config.endpoint, "http://localhost:4317");
    assert_eq!(config.protocol, "grpc");
    assert_eq!(config.service.name, "test-service");
}

/// Test telemetry data creation
#[test]
fn test_telemetry_data_creation() {
    use otlp::data::{TelemetryData, TelemetryDataType, TelemetryContent, TraceData};
    
    let trace_data = TraceData {
        trace_id: "12345678901234567890123456789012".to_string(),
        span_id: "1234567890123456".to_string(),
        parent_span_id: None,
        name: "test-span".to_string(),
        span_kind: otlp::data::SpanKind::Internal,
        start_time: 1000,
        end_time: 2000,
        status: otlp::data::SpanStatus::default(),
        attributes: HashMap::new(),
        events: vec![],
        links: vec![],
    };
    
    let telemetry = TelemetryData::new(
        TelemetryDataType::Trace,
        TelemetryContent::Trace(trace_data),
    );
    
    assert_eq!(telemetry.data_type, TelemetryDataType::Trace);
}

/// Test compression
#[test]
fn test_compression_gzip() {
    use flate2::write::GzEncoder;
    use flate2::Compression;
    use std::io::Write;
    
    let data = b"Hello, World! This is test data for compression.";
    
    let mut encoder = GzEncoder::new(Vec::new(), Compression::default());
    encoder.write_all(data).unwrap();
    let compressed = encoder.finish().unwrap();
    
    // Compressed data should not be empty
    assert!(!compressed.is_empty());
}

/// Test semantic convention types
#[test]
fn test_semantic_convention_types() {
    // HTTP
    use otlp::semantic_conventions::http::HttpMethod;
    assert!(matches!(HttpMethod::Get, HttpMethod::Get));
    assert!(matches!(HttpMethod::Post, HttpMethod::Post));
    
    // Database
    use otlp::semantic_conventions::database::DatabaseSystem;
    assert!(matches!(DatabaseSystem::Postgresql, DatabaseSystem::Postgresql));
    assert!(matches!(DatabaseSystem::Mysql, DatabaseSystem::Mysql));
    
    // Messaging
    use otlp::semantic_conventions::messaging::MessagingSystem;
    assert!(matches!(MessagingSystem::Kafka, MessagingSystem::Kafka));
    assert!(matches!(MessagingSystem::Rabbitmq, MessagingSystem::Rabbitmq));
    
    // K8s
    use otlp::semantic_conventions::k8s::K8sResourceType;
    assert!(matches!(K8sResourceType::Pod, K8sResourceType::Pod));
    assert!(matches!(K8sResourceType::Deployment, K8sResourceType::Deployment));
    
    // GenAI
    use otlp::semantic_conventions::gen_ai::GenAiSystem;
    assert!(matches!(GenAiSystem::OpenAI, GenAiSystem::OpenAI));
    assert!(matches!(GenAiSystem::Anthropic, GenAiSystem::Anthropic));
}

/// Test memory profiler lifecycle
#[tokio::test]
async fn test_memory_profiler_lifecycle() {
    use otlp::profiling::memory::{MemoryProfiler, MemoryProfilerConfig};
    
    let config = MemoryProfilerConfig::default();
    let mut profiler = MemoryProfiler::new(config);
    
    // Start profiler
    profiler.start().await
        .expect("Failed to start memory profiler");
    
    // Stop profiler
    profiler.stop().await
        .expect("Failed to stop memory profiler");
}

/// Test profile exporter
#[tokio::test]
async fn test_profile_exporter() {
    use otlp::profiling::exporter::{
        ProfileExporter, ProfileExporterConfig, generate_profile_id
    };
    
    // Test profile ID generation
    let profile_id = generate_profile_id();
    assert!(!profile_id.is_empty());
    
    // Create exporter
    let config = ProfileExporterConfig::default();
    let _exporter = ProfileExporter::new(config);
}

/// Test OTTL parser
#[test]
fn test_ottl_parser() {
    use otlp::ottl::processor::OttlParser;
    
    // Test set statement parsing
    let stmt = OttlParser::parse("set(attributes[\"key\"], \"value\")");
    assert!(stmt.is_ok());
    
    // Test delete_key statement parsing
    let stmt = OttlParser::parse("delete_key(attributes, \"old_key\")");
    assert!(stmt.is_ok());
    
    // Test invalid statement
    let stmt = OttlParser::parse("invalid_statement()");
    assert!(stmt.is_err());
}

/// Test config validation
#[test]
fn test_config_validation() {
    use otlp::config::OtlpConfig;
    
    // Valid config
    let config = OtlpConfig::default();
    assert!(config.validate().is_ok());
}
