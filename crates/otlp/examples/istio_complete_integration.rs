//! # Complete Istio Integration for OTLP
//!
//! 完整的Istio服务网格集成示例，展示OTLP在Istio环境中的深度集成
//!
//! ## 集成功能
//! - **EnvoyFilter**: 自定义Envoy配置
//! - **Telemetry v2**: Istio新版遥测
//! - **分布式追踪**: Trace传播和采样
//! - **Metrics收集**: RED指标
//! - **访问日志**: 结构化日志
//! - **故障注入**: 测试弹性
//!
//! ## Istio组件
//! - Envoy Proxy (Sidecar)
//! - Pilot (控制平面)
//! - Mixer (遥测收集)
//! - Galley (配置管理)
//!
//! ## 使用场景
//! - 微服务可观测性
//! - 服务网格监控
//! - 金丝雀发布
//! - A/B测试

use serde::{Deserialize, Serialize};
use serde_json::json;
use std::collections::HashMap;

// ============================================================================
// Part 1: Istio CRD Structures
// ============================================================================

/// EnvoyFilter - 自定义Envoy配置
#[derive(Debug, Serialize, Deserialize)]
pub struct EnvoyFilter {
    #[serde(rename = "apiVersion")]
    pub api_version: String,
    pub kind: String,
    pub metadata: Metadata,
    pub spec: EnvoyFilterSpec,
}

#[derive(Debug, Serialize, Deserialize)]
pub struct Metadata {
    pub name: String,
    pub namespace: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub labels: Option<HashMap<String, String>>,
}

#[derive(Debug, Serialize, Deserialize)]
pub struct EnvoyFilterSpec {
    #[serde(rename = "workloadSelector")]
    pub workload_selector: WorkloadSelector,
    #[serde(rename = "configPatches")]
    pub config_patches: Vec<ConfigPatch>,
}

#[derive(Debug, Serialize, Deserialize)]
pub struct WorkloadSelector {
    pub labels: HashMap<String, String>,
}

#[derive(Debug, Serialize, Deserialize)]
pub struct ConfigPatch {
    #[serde(rename = "applyTo")]
    pub apply_to: String,
    #[serde(rename = "match")]
    pub match_config: MatchConfig,
    pub patch: Patch,
}

#[derive(Debug, Serialize, Deserialize)]
pub struct MatchConfig {
    pub context: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub listener: Option<ListenerMatch>,
}

#[derive(Debug, Serialize, Deserialize)]
pub struct ListenerMatch {
    #[serde(rename = "filterChain")]
    pub filter_chain: FilterChainMatch,
}

#[derive(Debug, Serialize, Deserialize)]
pub struct FilterChainMatch {
    pub filter: FilterMatch,
}

#[derive(Debug, Serialize, Deserialize)]
pub struct FilterMatch {
    pub name: String,
}

#[derive(Debug, Serialize, Deserialize)]
pub struct Patch {
    pub operation: String,
    pub value: serde_json::Value,
}

// ============================================================================
// Part 2: Telemetry v2 Configuration
// ============================================================================

/// Telemetry CRD - Istio Telemetry v2配置
#[derive(Debug, Serialize, Deserialize)]
pub struct Telemetry {
    #[serde(rename = "apiVersion")]
    pub api_version: String,
    pub kind: String,
    pub metadata: Metadata,
    pub spec: TelemetrySpec,
}

#[derive(Debug, Serialize, Deserialize)]
pub struct TelemetrySpec {
    #[serde(skip_serializing_if = "Option::is_none")]
    pub selector: Option<WorkloadSelector>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub tracing: Option<Vec<TracingConfig>>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub metrics: Option<Vec<MetricsConfig>>,
    #[serde(skip_serializing_if = "Option::is_none")]
    #[serde(rename = "accessLogging")]
    pub access_logging: Option<Vec<AccessLoggingConfig>>,
}

#[derive(Debug, Serialize, Deserialize)]
pub struct TracingConfig {
    pub providers: Vec<TracingProvider>,
    #[serde(rename = "randomSamplingPercentage")]
    pub random_sampling_percentage: f64,
    #[serde(rename = "customTags")]
    pub custom_tags: HashMap<String, CustomTag>,
}

#[derive(Debug, Serialize, Deserialize)]
pub struct TracingProvider {
    pub name: String,
}

#[derive(Debug, Serialize, Deserialize)]
pub struct CustomTag {
    pub literal: Option<LiteralValue>,
    pub environment: Option<EnvironmentValue>,
    pub header: Option<HeaderValue>,
}

#[derive(Debug, Serialize, Deserialize)]
pub struct LiteralValue {
    pub value: String,
}

#[derive(Debug, Serialize, Deserialize)]
pub struct EnvironmentValue {
    pub name: String,
    #[serde(rename = "defaultValue")]
    pub default_value: Option<String>,
}

#[derive(Debug, Serialize, Deserialize)]
pub struct HeaderValue {
    pub name: String,
    #[serde(rename = "defaultValue")]
    pub default_value: Option<String>,
}

#[derive(Debug, Serialize, Deserialize)]
pub struct MetricsConfig {
    pub providers: Vec<MetricsProvider>,
    pub overrides: Vec<MetricsOverride>,
}

#[derive(Debug, Serialize, Deserialize)]
pub struct MetricsProvider {
    pub name: String,
}

#[derive(Debug, Serialize, Deserialize)]
pub struct MetricsOverride {
    #[serde(rename = "match")]
    pub match_config: MetricsMatch,
    pub disabled: bool,
}

#[derive(Debug, Serialize, Deserialize)]
pub struct MetricsMatch {
    pub metric: String,
    pub mode: String,
}

#[derive(Debug, Serialize, Deserialize)]
pub struct AccessLoggingConfig {
    pub providers: Vec<AccessLoggingProvider>,
}

#[derive(Debug, Serialize, Deserialize)]
pub struct AccessLoggingProvider {
    pub name: String,
}

// ============================================================================
// Part 3: OTLP EnvoyFilter for Tracing
// ============================================================================

pub fn create_otlp_tracing_envoyfilter() -> EnvoyFilter {
    let mut labels = HashMap::new();
    labels.insert("app".to_string(), "productpage".to_string());

    EnvoyFilter {
        api_version: "networking.istio.io/v1alpha3".to_string(),
        kind: "EnvoyFilter".to_string(),
        metadata: Metadata {
            name: "otlp-tracing-filter".to_string(),
            namespace: "default".to_string(),
            labels: None,
        },
        spec: EnvoyFilterSpec {
            workload_selector: WorkloadSelector { labels },
            config_patches: vec![ConfigPatch {
                apply_to: "HTTP_FILTER".to_string(),
                match_config: MatchConfig {
                    context: "SIDECAR_INBOUND".to_string(),
                    listener: Some(ListenerMatch {
                        filter_chain: FilterChainMatch {
                            filter: FilterMatch {
                                name: "envoy.filters.network.http_connection_manager".to_string(),
                            },
                        },
                    }),
                },
                patch: Patch {
                    operation: "INSERT_BEFORE".to_string(),
                    value: json!({
                        "name": "envoy.filters.http.grpc_stats",
                        "typed_config": {
                            "@type": "type.googleapis.com/envoy.extensions.filters.http.grpc_stats.v3.FilterConfig",
                            "emit_filter_state": true,
                            "stats_for_all_methods": true
                        }
                    }),
                },
            }],
        },
    }
}

// ============================================================================
// Part 4: Telemetry v2 for OTLP
// ============================================================================

pub fn create_otlp_telemetry() -> Telemetry {
    let mut custom_tags = HashMap::new();
    custom_tags.insert(
        "cluster_name".to_string(),
        CustomTag {
            literal: Some(LiteralValue {
                value: "production-cluster".to_string(),
            }),
            environment: None,
            header: None,
        },
    );
    custom_tags.insert(
        "user_agent".to_string(),
        CustomTag {
            literal: None,
            environment: None,
            header: Some(HeaderValue {
                name: "user-agent".to_string(),
                default_value: Some("unknown".to_string()),
            }),
        },
    );

    Telemetry {
        api_version: "telemetry.istio.io/v1alpha1".to_string(),
        kind: "Telemetry".to_string(),
        metadata: Metadata {
            name: "otlp-telemetry".to_string(),
            namespace: "istio-system".to_string(),
            labels: None,
        },
        spec: TelemetrySpec {
            selector: None, // Apply to all workloads
            tracing: Some(vec![TracingConfig {
                providers: vec![TracingProvider {
                    name: "otlp".to_string(),
                }],
                random_sampling_percentage: 10.0,
                custom_tags,
            }]),
            metrics: Some(vec![MetricsConfig {
                providers: vec![MetricsProvider {
                    name: "prometheus".to_string(),
                }],
                overrides: vec![],
            }]),
            access_logging: Some(vec![AccessLoggingConfig {
                providers: vec![AccessLoggingProvider {
                    name: "otlp".to_string(),
                }],
            }]),
        },
    }
}

// ============================================================================
// Part 5: MeshConfig for OTLP Extension Provider
// ============================================================================

pub fn create_otlp_extension_provider_config() -> serde_json::Value {
    json!({
        "extensionProviders": [
            {
                "name": "otlp",
                "opentelemetry": {
                    "service": "otlp-collector.observability.svc.cluster.local",
                    "port": 4317,
                    "resource_detectors": {
                        "environment": {},
                        "dynatrace": {}
                    }
                }
            },
            {
                "name": "otlp-http",
                "opentelemetry": {
                    "service": "otlp-collector.observability.svc.cluster.local",
                    "port": 4318,
                    "http": {
                        "path": "/v1/traces",
                        "timeout": "5s"
                    }
                }
            }
        ],
        "defaultConfig": {
            "tracing": {
                "sampling": 10.0,
                "zipkin": {
                    "address": "otlp-collector.observability:9411"
                }
            }
        }
    })
}

// ============================================================================
// Part 6: Virtual Service for Canary Deployment
// ============================================================================

#[derive(Debug, Serialize, Deserialize)]
pub struct VirtualService {
    #[serde(rename = "apiVersion")]
    pub api_version: String,
    pub kind: String,
    pub metadata: Metadata,
    pub spec: VirtualServiceSpec,
}

#[derive(Debug, Serialize, Deserialize)]
pub struct VirtualServiceSpec {
    pub hosts: Vec<String>,
    pub http: Vec<HttpRoute>,
}

#[derive(Debug, Serialize, Deserialize)]
pub struct HttpRoute {
    #[serde(skip_serializing_if = "Option::is_none")]
    #[serde(rename = "match")]
    pub match_rules: Option<Vec<HttpMatchRequest>>,
    pub route: Vec<HTTPRouteDestination>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub fault: Option<HttpFaultInjection>,
}

#[derive(Debug, Serialize, Deserialize)]
pub struct HttpMatchRequest {
    #[serde(skip_serializing_if = "Option::is_none")]
    pub headers: Option<HashMap<String, HeaderMatch>>,
}

#[derive(Debug, Serialize, Deserialize)]
pub struct HeaderMatch {
    pub exact: String,
}

#[derive(Debug, Serialize, Deserialize)]
pub struct HTTPRouteDestination {
    pub destination: Destination,
    pub weight: u32,
}

#[derive(Debug, Serialize, Deserialize)]
pub struct Destination {
    pub host: String,
    pub subset: String,
}

#[derive(Debug, Serialize, Deserialize)]
pub struct HttpFaultInjection {
    #[serde(skip_serializing_if = "Option::is_none")]
    pub delay: Option<FaultDelay>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub abort: Option<FaultAbort>,
}

#[derive(Debug, Serialize, Deserialize)]
pub struct FaultDelay {
    pub percentage: PercentageValue,
    #[serde(rename = "fixedDelay")]
    pub fixed_delay: String,
}

#[derive(Debug, Serialize, Deserialize)]
pub struct FaultAbort {
    pub percentage: PercentageValue,
    #[serde(rename = "httpStatus")]
    pub http_status: u32,
}

#[derive(Debug, Serialize, Deserialize)]
pub struct PercentageValue {
    pub value: f64,
}

pub fn create_canary_virtual_service() -> VirtualService {
    let mut canary_header = HashMap::new();
    canary_header.insert(
        "canary".to_string(),
        HeaderMatch {
            exact: "true".to_string(),
        },
    );

    VirtualService {
        api_version: "networking.istio.io/v1beta1".to_string(),
        kind: "VirtualService".to_string(),
        metadata: Metadata {
            name: "reviews-canary".to_string(),
            namespace: "default".to_string(),
            labels: None,
        },
        spec: VirtualServiceSpec {
            hosts: vec!["reviews.default.svc.cluster.local".to_string()],
            http: vec![
                // Canary route (10% traffic or with canary header)
                HttpRoute {
                    match_rules: Some(vec![HttpMatchRequest {
                        headers: Some(canary_header),
                    }]),
                    route: vec![HTTPRouteDestination {
                        destination: Destination {
                            host: "reviews".to_string(),
                            subset: "v2".to_string(),
                        },
                        weight: 100,
                    }],
                    fault: None,
                },
                // Production route (90% traffic)
                HttpRoute {
                    match_rules: None,
                    route: vec![
                        HTTPRouteDestination {
                            destination: Destination {
                                host: "reviews".to_string(),
                                subset: "v1".to_string(),
                            },
                            weight: 90,
                        },
                        HTTPRouteDestination {
                            destination: Destination {
                                host: "reviews".to_string(),
                                subset: "v2".to_string(),
                            },
                            weight: 10,
                        },
                    ],
                    fault: None,
                },
            ],
        },
    }
}

// ============================================================================
// Part 7: Destination Rule
// ============================================================================

#[derive(Debug, Serialize, Deserialize)]
pub struct DestinationRule {
    #[serde(rename = "apiVersion")]
    pub api_version: String,
    pub kind: String,
    pub metadata: Metadata,
    pub spec: DestinationRuleSpec,
}

#[derive(Debug, Serialize, Deserialize)]
pub struct DestinationRuleSpec {
    pub host: String,
    pub subsets: Vec<Subset>,
    #[serde(skip_serializing_if = "Option::is_none")]
    #[serde(rename = "trafficPolicy")]
    pub traffic_policy: Option<TrafficPolicy>,
}

#[derive(Debug, Serialize, Deserialize)]
pub struct Subset {
    pub name: String,
    pub labels: HashMap<String, String>,
}

#[derive(Debug, Serialize, Deserialize)]
pub struct TrafficPolicy {
    #[serde(rename = "connectionPool")]
    pub connection_pool: ConnectionPoolSettings,
    #[serde(rename = "outlierDetection")]
    pub outlier_detection: OutlierDetection,
}

#[derive(Debug, Serialize, Deserialize)]
pub struct ConnectionPoolSettings {
    pub tcp: TcpSettings,
    pub http: HttpSettings,
}

#[derive(Debug, Serialize, Deserialize)]
pub struct TcpSettings {
    #[serde(rename = "maxConnections")]
    pub max_connections: u32,
}

#[derive(Debug, Serialize, Deserialize)]
pub struct HttpSettings {
    #[serde(rename = "http1MaxPendingRequests")]
    pub http1_max_pending_requests: u32,
    #[serde(rename = "http2MaxRequests")]
    pub http2_max_requests: u32,
}

#[derive(Debug, Serialize, Deserialize)]
pub struct OutlierDetection {
    #[serde(rename = "consecutiveErrors")]
    pub consecutive_errors: u32,
    pub interval: String,
    #[serde(rename = "baseEjectionTime")]
    pub base_ejection_time: String,
}

pub fn create_destination_rule_with_circuit_breaker() -> DestinationRule {
    let mut v1_labels = HashMap::new();
    v1_labels.insert("version".to_string(), "v1".to_string());

    let mut v2_labels = HashMap::new();
    v2_labels.insert("version".to_string(), "v2".to_string());

    DestinationRule {
        api_version: "networking.istio.io/v1beta1".to_string(),
        kind: "DestinationRule".to_string(),
        metadata: Metadata {
            name: "reviews-circuit-breaker".to_string(),
            namespace: "default".to_string(),
            labels: None,
        },
        spec: DestinationRuleSpec {
            host: "reviews.default.svc.cluster.local".to_string(),
            subsets: vec![
                Subset {
                    name: "v1".to_string(),
                    labels: v1_labels,
                },
                Subset {
                    name: "v2".to_string(),
                    labels: v2_labels,
                },
            ],
            traffic_policy: Some(TrafficPolicy {
                connection_pool: ConnectionPoolSettings {
                    tcp: TcpSettings {
                        max_connections: 100,
                    },
                    http: HttpSettings {
                        http1_max_pending_requests: 10,
                        http2_max_requests: 100,
                    },
                },
                outlier_detection: OutlierDetection {
                    consecutive_errors: 5,
                    interval: "30s".to_string(),
                    base_ejection_time: "30s".to_string(),
                },
            }),
        },
    }
}

// ============================================================================
// Part 8: Complete Deployment Example
// ============================================================================

pub fn generate_complete_istio_otlp_config() -> String {
    let configs = vec![
        (
            "EnvoyFilter",
            serde_yaml::to_string(&create_otlp_tracing_envoyfilter()).unwrap(),
        ),
        (
            "Telemetry",
            serde_yaml::to_string(&create_otlp_telemetry()).unwrap(),
        ),
        (
            "VirtualService",
            serde_yaml::to_string(&create_canary_virtual_service()).unwrap(),
        ),
        (
            "DestinationRule",
            serde_yaml::to_string(&create_destination_rule_with_circuit_breaker()).unwrap(),
        ),
    ];

    configs
        .iter()
        .map(|(name, yaml)| format!("---\n# {}\n{}", name, yaml))
        .collect::<Vec<_>>()
        .join("\n")
}

// ============================================================================
// Main Function - Generate Configuration
// ============================================================================

fn main() {
    println!("🚀 Generating Complete Istio + OTLP Integration Configuration\n");

    // 1. EnvoyFilter for OTLP Tracing
    println!("📝 1. EnvoyFilter for OTLP Tracing:");
    println!("---");
    println!(
        "{}",
        serde_yaml::to_string(&create_otlp_tracing_envoyfilter()).unwrap()
    );

    // 2. Telemetry v2 Configuration
    println!("\n📝 2. Telemetry v2 Configuration:");
    println!("---");
    println!(
        "{}",
        serde_yaml::to_string(&create_otlp_telemetry()).unwrap()
    );

    // 3. MeshConfig Extension Provider
    println!("\n📝 3. MeshConfig OTLP Extension Provider:");
    println!("---");
    println!(
        "{}",
        serde_yaml::to_string(&create_otlp_extension_provider_config()).unwrap()
    );

    // 4. Canary Deployment Virtual Service
    println!("\n📝 4. Canary Deployment Virtual Service:");
    println!("---");
    println!(
        "{}",
        serde_yaml::to_string(&create_canary_virtual_service()).unwrap()
    );

    // 5. Destination Rule with Circuit Breaker
    println!("\n📝 5. Destination Rule with Circuit Breaker:");
    println!("---");
    println!(
        "{}",
        serde_yaml::to_string(&create_destination_rule_with_circuit_breaker()).unwrap()
    );

    // Complete Configuration
    println!("\n📦 Complete Configuration File:");
    println!("================================================================================");
    println!("{}", generate_complete_istio_otlp_config());

    println!("\n✅ Configuration generation completed!");
    println!("\n💡 Usage:");
    println!("   kubectl apply -f istio-otlp-config.yaml");
    println!("\n📊 Monitor with:");
    println!("   kubectl get telemetry -A");
    println!("   kubectl get envoyfilter -A");
    println!("   kubectl get virtualservice");
}
