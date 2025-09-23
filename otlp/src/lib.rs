//! # OpenTelemetry Protocol (OTLP) Implementation for Rust 1.90
//! 
//! 本库提供了基于Rust 1.90语言特性的OpenTelemetry协议(OTLP)完整实现，
//! 支持同步和异步结合的遥测数据收集、处理和传输。
//! 
//! ## 核心特性
//! 
//! - **异步优先设计**: 利用Rust 1.90的async/await特性实现高性能异步处理
//! - **同步兼容**: 提供同步API接口，支持传统同步代码集成
//! - **多传输协议**: 支持gRPC和HTTP/JSON两种OTLP传输方式
//! - **类型安全**: 利用Rust类型系统确保编译时安全性
//! - **零拷贝优化**: 使用Rust 1.90的内存管理特性优化性能
//! - **并发安全**: 基于Rust的所有权系统实现无锁并发
//! 
//! ## 架构设计
//! 
//! ```text
//! ┌─────────────────┐    ┌─────────────────┐    ┌─────────────────┐
//! │   数据收集层     │    │   数据处理层     │    │   数据传输层     │
//! │  (Collection)   │──▶│  (Processing)   │──▶│  (Transport)    │
//! │                 │    │                 │    │                 │
//! │ • Traces        │    │ • 过滤/聚合      │    │ • gRPC          │
//! │ • Metrics       │    │ • 批处理        │    │ • HTTP/JSON     │
//! │ • Logs          │    │ • 压缩          │    │ • 重试机制      │
//! └─────────────────┘    └─────────────────┘    └─────────────────┘
//! ```
//! 
//! ## 使用示例
//! 
//! ```rust
//! use otlp::{OtlpConfig, TraceData};
//! 
//! #[tokio::main]
//! async fn main() -> Result<(), Box<dyn std::error::Error>> {
//!     // 创建OTLP配置
//!     let config = OtlpConfig::new()
//!         .with_endpoint("http://localhost:4317")
//!         .with_connect_timeout(std::time::Duration::from_secs(5));
//!     
//!     // 创建追踪数据
//!     let trace_data = TraceData {
//!         trace_id: "example-trace-id".to_string(),
//!         span_id: "example-span-id".to_string(),
//!         parent_span_id: None,
//!         name: "example-operation".to_string(),
//!         span_kind: otlp::data::SpanKind::Internal,
//!         start_time: 0,
//!         end_time: 1000000,
//!         status: otlp::data::SpanStatus::default(),
//!         attributes: std::collections::HashMap::new(),
//!         events: vec![],
//!         links: vec![],
//!     };
//!     
//!     println!("追踪数据: {:?}", trace_data);
//!     
//!     Ok(())
//! }
//! ```

pub mod client;
pub mod config;
pub mod data;
pub mod error;
pub mod exporter;
pub mod processor;
pub mod protobuf;
pub mod transport;
pub mod utils;
pub mod microservices;
pub mod benchmarks;
pub mod ai_ml;
pub mod edge_computing;
pub mod blockchain;
pub mod resilience;

// 重新导出主要类型
pub use client::{OtlpClient, OtlpClientBuilder, TraceBuilder, MetricBuilder, LogBuilder};
pub use config::{OtlpConfig, OtlpConfigBuilder, TransportProtocol, Compression};
pub use data::{TelemetryData, TraceData, MetricData, LogData, AttributeValue, StatusCode};
pub use error::{OtlpError, Result};
pub use exporter::{OtlpExporter, ExportResult, ExporterMetrics};
pub use processor::{OtlpProcessor, ProcessingConfig, ProcessorMetrics};
pub use transport::{Transport, GrpcTransport, HttpTransport, TransportFactory};
pub use utils::{CompressionUtils, TimeUtils, StringUtils, HashUtils, BatchUtils, RetryUtils, PerformanceUtils};
pub use resilience::{ResilienceManager, ResilienceConfig, ResilienceError};

// 重新导出微服务相关类型
pub use microservices::{
    LoadBalancer, RoundRobinLoadBalancer, WeightedRoundRobinLoadBalancer,
    CircuitBreaker, CircuitBreakerConfig, CircuitBreakerState,
    Retryer, RetryConfig,
    ServiceDiscoveryClient, ServiceEndpoint, HealthStatus,
    MicroserviceClient, MockConsulClient,
    // 高级微服务功能
    ServiceMeshConfig, ServiceMeshType, SidecarConfig, ResourceLimits,
    RoutingRule, MatchCondition, Destination, RetryPolicy, CircuitBreakerPolicy,
    IntelligentRouter, TrafficManager, HealthChecker, ServiceInstance, InstanceMetrics,
    RouterMetrics, RouteRequest, RouteResponse, RoutingError,
    AdaptiveLoadBalancer, FaultInjector, FaultConfig, FaultType, FaultResult,
};

// 版本信息
pub const VERSION: &str = env!("CARGO_PKG_VERSION");
pub const RUST_VERSION: &str = "1.90";

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_version_info() {
        assert!(!VERSION.is_empty());
        assert_eq!(RUST_VERSION, "1.90");
    }
}
