//! # OpenTelemetry Protocol (OTLP) Implementation for Rust 1.90
//!
//! 本库提供了基于Rust 1.90语言特性的OpenTelemetry协议(OTLP)完整实现，
//! 支持同步和异步结合的遥测数据收集、处理和传输。
//!
//! ## 设计理念
//!
//! 本库基于以下核心设计理念构建：
//!
//! 1. **性能优先**: 利用Rust 1.90的性能特性，实现零拷贝、无锁并发的高性能处理
//! 2. **类型安全**: 利用Rust类型系统在编译时捕获错误，避免运行时异常
//! 3. **异步优先**: 基于tokio异步运行时，支持高并发和低延迟处理
//! 4. **可观测性**: 内置完整的监控、日志和指标收集机制
//! 5. **可扩展性**: 模块化设计，支持插件和自定义扩展
//! 6. **标准化**: 完全兼容OpenTelemetry规范，确保跨语言互操作性
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
//! ## 技术架构
//!
//! ### 1. 数据收集层 (Collection Layer)
//! - **Traces**: 分布式追踪数据收集和处理
//! - **Metrics**: 指标数据的收集和聚合
//! - **Logs**: 日志数据的收集和结构化处理
//! - **Events**: 自定义事件和业务指标的收集
//! - **System Metrics**: 系统级指标（CPU、内存、网络等）
//!
//! ### 2. 数据处理层 (Processing Layer)
//! - **过滤和聚合**: 数据过滤、聚合和转换
//! - **批处理**: 高效的批量数据处理
//! - **压缩**: 数据压缩减少传输开销
//! - **ML预测**: 基于机器学习的错误预测
//! - **异常检测**: 实时异常模式识别
//!
//! ### 3. 数据传输层 (Transport Layer)
//! - **gRPC**: 高性能二进制协议传输
//! - **HTTP/JSON**: 标准HTTP协议传输
//! - **重试机制**: 智能重试和故障恢复
//! - **负载均衡**: 多目标负载均衡
//! - **熔断器**: 故障隔离和快速失败
//!
//! ### 4. 分布式协调层 (Coordination Layer)
//! - **集群管理**: 节点发现、注册和健康检查
//! - **共识协议**: Raft、PBFT等分布式一致性算法
//! - **错误传播**: 基于DAG的错误传播图管理
//! - **恢复协调**: 跨节点的分布式恢复策略
//! - **Gossip协议**: 高效的信息传播和同步
//!
//! ### 5. 边缘计算层 (Edge Computing Layer)
//! - **边缘节点管理**: 边缘节点的发现和注册
//! - **任务调度**: 智能任务分发和负载均衡
//! - **资源管理**: 边缘资源的动态分配和回收
//! - **数据同步**: 边缘与云端的数据一致性
//! - **自适应调度**: 基于网络状况的动态调整
//!
//! ### 6. 监控告警层 (Monitoring Layer)
//! - **实时监控**: 系统状态的实时监控
//! - **告警系统**: 智能告警和通知机制
//! - **性能分析**: 性能指标收集和分析
//! - **趋势预测**: 基于历史数据的趋势预测
//! - **可视化**: 丰富的监控仪表板和图表
//!
//! ## 性能特性
//!
//! ### 1. 高性能处理
//! - **零拷贝**: 最小化内存拷贝操作
//! - **无锁并发**: 基于Rust所有权系统的无锁数据结构
//! - **异步I/O**: 基于tokio的高性能异步I/O
//! - **批量处理**: 高效的批量数据处理
//! - **连接池**: 连接复用和池化管理
//!
//! ### 2. 内存优化
//! - **智能内存管理**: 基于Rust 1.90的内存管理特性
//! - **对象池**: 对象重用减少GC压力
//! - **缓存优化**: 智能缓存策略和LRU淘汰
//! - **内存映射**: 大文件的内存映射处理
//! - **压缩存储**: 数据压缩减少内存占用
//!
//! ### 3. 网络优化
//! - **HTTP/2**: 多路复用和头部压缩
//! - **gRPC**: 高效的二进制协议
//! - **连接复用**: 减少连接建立开销
//! - **数据压缩**: gzip、snappy等压缩算法
//! - **CDN集成**: 静态资源CDN加速
//!
//! ## 可靠性保证
//!
//! ### 1. 容错机制
//! - **熔断器**: 防止级联故障
//! - **重试策略**: 指数退避和抖动
//! - **超时控制**: 多层超时保护
//! - **优雅降级**: 保持核心功能可用
//! - **故障转移**: 自动故障检测和转移
//!
//! ### 2. 一致性保证
//! - **强一致性**: 基于Raft的强一致性
//! - **最终一致性**: 基于Gossip的最终一致性
//! - **弱一致性**: 性能优化的弱一致性
//! - **事务支持**: 分布式事务支持
//! - **版本控制**: 数据版本和冲突解决
//!
//! ### 3. 安全性
//! - **TLS加密**: 传输层加密保护
//! - **认证授权**: 基于JWT的认证机制
//! - **访问控制**: 细粒度权限控制
//! - **审计日志**: 完整的操作审计
//! - **数据脱敏**: 敏感数据脱敏处理
//!
//! ## 扩展性设计
//!
//! ### 1. 模块化架构
//! - **插件系统**: 支持自定义插件扩展
//! - **接口抽象**: 清晰的接口定义和实现
//! - **配置驱动**: 基于配置的灵活部署
//! - **热更新**: 支持配置和代码热更新
//! - **版本兼容**: 向后兼容的版本管理
//!
//! ### 2. 水平扩展
//! - **无状态设计**: 支持水平扩展
//! - **负载均衡**: 智能负载分发
//! - **数据分片**: 数据水平分片
//! - **服务发现**: 动态服务发现
//! - **自动扩缩容**: 基于指标的自动扩缩容
//!
//! ### 3. 垂直扩展
//! - **多核优化**: 充分利用多核CPU
//! - **内存优化**: 高效内存使用
//! - **I/O优化**: 异步I/O和批量处理
//! - **缓存优化**: 多级缓存策略
//! - **算法优化**: 高效算法实现
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
