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
//! - **智能错误预测**: 集成机器学习算法进行错误预测和异常检测
//! - **分布式协调**: 支持跨节点的分布式错误处理和恢复协调
//! - **边缘计算**: 提供边缘节点管理和自适应调度能力
//! - **容错机制**: 实现熔断器、重试、负载均衡等容错模式
//!
//! ## 架构设计
//!
//! ```text
//! ┌─────────────────┐    ┌─────────────────┐    ┌─────────────────┐
//! │   数据收集层     │    │   数据处理层     │    │   数据传输层     │
//! │  (Collection)   │──▶│  (Processing)    │──▶│  (Transport)    │
//! │                 │    │                 │    │                 │
//! │ • Traces        │    │ • 过滤/聚合      │    │ • gRPC          │
//! │ • Metrics       │    │ • 批处理         │    │ • HTTP/JSON     │
//! │ • Logs          │    │ • 压缩           │    │ • 重试机制      │
//! │ • 错误事件       │    │ • ML预测         │    │ • 负载均衡      │
//! │ • 系统指标       │    │ • 异常检测       │    │ • 熔断器        │
//! └─────────────────┘    └─────────────────┘    └─────────────────┘
//!           │                       │                       │
//!           ▼                       ▼                       ▼
//! ┌─────────────────┐    ┌─────────────────┐    ┌─────────────────┐
//! │   分布式协调层   │    │   边缘计算层     │    │   监控告警层     │
//! │ (Coordination)  │    │ (Edge Computing)│    │  (Monitoring)   │
//! │                 │    │                 │    │                 │
//! │ • 集群管理       │    │ • 边缘节点管理   │    │ • 实时监控       │
//! │ • 共识协议       │    │ • 任务调度       │    │ • 告警系统       │
//! │ • 错误传播       │    │ • 资源管理       │    │ • 性能分析       │
//! │ • 恢复协调       │    │ • 数据同步       │    │ • 趋势预测       │
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

pub mod ai_ml;
pub mod benchmarks;
pub mod blockchain;
pub mod client;
pub mod config;
pub mod data;
pub mod distributed_coordination;
pub mod edge_computing;
pub mod error;
pub mod exporter;
pub mod microservices;
pub mod ml_error_prediction;
pub mod monitoring;
pub mod performance_optimization;
pub mod processor;
pub mod protobuf;
pub mod resilience;
pub mod transport;
pub mod utils;

// 重新导出主要类型
pub use client::{LogBuilder, MetricBuilder, OtlpClient, OtlpClientBuilder, TraceBuilder};
pub use config::{Compression, OtlpConfig, OtlpConfigBuilder, TransportProtocol};
pub use data::{AttributeValue, LogData, MetricData, StatusCode, TelemetryData, TraceData};
pub use distributed_coordination::{
    ClusterStatus, CoordinationResult, DistributedConfig, DistributedError,
    DistributedErrorCoordinator,
};
pub use error::{ErrorCategory, ErrorContext, ErrorSeverity, OtlpError, Result};
pub use exporter::{ExportResult, ExporterMetrics, OtlpExporter};
pub use ml_error_prediction::{
    ErrorSample, MLErrorPrediction, MLPredictionConfig, PredictionFeedback, PredictionResult,
    SystemContext,
};
pub use monitoring::{
    AlertCondition, AlertRule, ErrorEvent, ErrorMonitoringSystem, MonitoringConfig,
    MonitoringMetrics,
};
pub use performance_optimization::{
    BenchmarkResults, OptimizedError, PerformanceConfig, PerformanceMetrics, PerformanceOptimizer,
};
pub use processor::{OtlpProcessor, ProcessingConfig, ProcessorMetrics};
pub use resilience::{ResilienceConfig, ResilienceError, ResilienceManager};
pub use transport::{GrpcTransport, HttpTransport, Transport, TransportFactory};
pub use utils::{
    BatchUtils, CompressionUtils, HashUtils, PerformanceUtils, RetryUtils, StringUtils, TimeUtils,
};

// 重新导出微服务相关类型
pub use microservices::{
    AdaptiveLoadBalancer,
    CircuitBreaker,
    CircuitBreakerConfig,
    CircuitBreakerPolicy,
    CircuitBreakerState,
    Destination,
    FaultConfig,
    FaultInjector,
    FaultResult,
    FaultType,
    HealthChecker,
    HealthStatus,
    InstanceMetrics,
    IntelligentRouter,
    LoadBalancer,
    MatchCondition,
    MicroserviceClient,
    MockConsulClient,
    ResourceLimits,
    RetryConfig,
    RetryPolicy,
    Retryer,
    RoundRobinLoadBalancer,
    RouteRequest,
    RouteResponse,
    RouterMetrics,
    RoutingError,
    RoutingRule,
    ServiceDiscoveryClient,
    ServiceEndpoint,
    ServiceInstance,
    // 高级微服务功能
    ServiceMeshConfig,
    ServiceMeshType,
    SidecarConfig,
    TrafficManager,
    WeightedRoundRobinLoadBalancer,
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
